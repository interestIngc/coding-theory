#include <iostream>
#include <vector>
#include <algorithm>
#include <cmath>
#include <chrono>
#include <random>

using uint = unsigned int;

struct Edge {
    uint from;
    bool c;

    Edge() {
        from = 0;
        c = false;
    }

    explicit Edge(uint from, bool c) {
        this->from = from;
        this->c = c;
    }
};

struct Node {
    std::vector<Edge> edges;

    Node() {
        this->edges = std::vector<Edge>();
    }

    explicit Node(std::vector<Edge>& edges) {
        this->edges = edges;
    }
};

class RandomGenerator {
public:
    static double nextEta(double sigma) {
        unsigned seed = std::chrono::system_clock::now().time_since_epoch().count();
        static std::default_random_engine generator(seed);
        std::normal_distribution<double> noise_distribution(0, sigma);
        return noise_distribution(generator);
    }

    static int nextBit() {
        static std::random_device rd;
        static std::uniform_int_distribution<int> bit_distribution(0, 1);
        return bit_distribution(rd);
    }
};

class BinaryVector {
private:
    std::vector<bool> v;
public:
    explicit BinaryVector() {
        this->v = std::vector<bool>();
    }

    explicit BinaryVector(std::vector<bool>& v) {
        this->v = v;
    }

    explicit BinaryVector(int n) {
        v.assign(n, false);
    }

    int size() {
        return v.size();
    }

    bool operator[](int i) {
        return v[i];
    }

    void operator+=(BinaryVector& other) {
        int n = size();

        for (int i = 0; i < n; i++) {
            v[i] = v[i] ^ other[i];
        }
    }

    friend std::istream &operator>>(std::istream& is, BinaryVector& binary_vector) {
        for (int i = 0; i < binary_vector.size(); i++) {
            int num;
            is >> num;
            if (num > 0) {
                binary_vector.v[i] = true;
            }
        }
        return is;
    }

    friend std::ostream &operator<<(std::ostream& os, BinaryVector& binary_vector) {
        for (bool bit : binary_vector.v) {
            os << (int) bit << " ";
        }
        return os;
    }
};

class Matrix {
private:
    std::vector<BinaryVector> g;
public:
    int k = 0;
    int n = 0;

    explicit Matrix() {
        g = std::vector<BinaryVector>();
    }

    explicit Matrix(int k, int n) {
        this->k = k;
        this->n = n;
        g = std::vector<BinaryVector>(k, BinaryVector(n));
    }

    BinaryVector& operator[](int i) {
        return g[i];
    }

    friend std::istream& operator>>(std::istream& is, Matrix& matrix) {
        for (int i = 0; i < matrix.k; i++) {
            std::cin >> matrix.g[i];
        }
        return is;
    }
};

/*
 * Приведение порождающей матрицы к минимальной спэновой форме
 */
class MSF {
public:
    Matrix msf_g;
    std::vector<int> start_indexes;
    std::vector<int> end_indexes;

    explicit MSF(Matrix& msf_g, std::vector<int>& start_indexes, std::vector<int>& end_indexes) {
        this->msf_g = msf_g;
        this->start_indexes = start_indexes;
        this->end_indexes = end_indexes;
    }

    static MSF to_minimal_span_form(Matrix matrix) {
        int n = matrix.n;
        int k = matrix.k;
        Matrix msf_g = matrix;

        int row_ind = 0;
        for (int j = 0; j < matrix.n && row_ind < k - 1; j++) {
            int current = row_ind;
            for (; current < k; current++) {
                if (msf_g[current][j]) {
                    break;
                }
            }
            if (current < k) {
                std::swap(msf_g[row_ind], msf_g[current]);
                for (int i = row_ind + 1; i < k; i++) {
                    if (msf_g[i][j]) {
                        msf_g[i] += msf_g[row_ind];
                    }
                }
                row_ind++;
            }
        }

        int num_of_ended = 0;
        std::vector<bool> ended(k, false);
        for (int j = matrix.n - 1; j >= 0 && num_of_ended < k - 1; j--) {
            int last_one = k - 1;
            for (; last_one >= 0; last_one--) {
                if (!ended[last_one] && msf_g[last_one][j]) {
                    break;
                }
            }
            if (last_one >= 0) {
                for (int i = 0; i < k; i++) {
                    if (i == last_one) continue;
                    if (!ended[i] && msf_g[i][j]) {
                        msf_g[i] += msf_g[last_one];
                    }
                }
                ended[last_one] = true;
                num_of_ended++;
            }
        }

        std::vector<int> start_indexes(k, -1);
        std::vector<int> end_indexes(k, -1);

        for (int i = 0; i < k; i++) {
            for (int j = 0; j < n; j++) {
                if (msf_g[i][j]) {
                    start_indexes[i] = j;
                    break;
                }
            }
            for (int j = n - 1; j >= 0; j--) {
                if (msf_g[i][j]) {
                    end_indexes[i] = j;
                    break;
                }
            }
        }

        return MSF(msf_g, start_indexes, end_indexes);
    }
};

/*
 * Построение решетки по порождающей матрице в минимальной спэновой форме
 */
namespace Trellis {
    std::vector<std::vector<Node>> graph;

    uint index_to_mask(uint index, uint active_bit_mask) {
        uint mask = 0;
        uint last_active_bit = 1;
        for (; active_bit_mask > 0; active_bit_mask >>= 1, last_active_bit <<= 1) {
            uint active_bit = active_bit_mask & 1u;
            if (active_bit == 0) continue;

            uint curr_bit = index & 1u;
            if (curr_bit > 0) {
                mask |= last_active_bit;
            }
            index >>= 1;
        }
        return mask;
    }

    uint mask_to_index(uint mask, uint active_bit_mask) {
        uint index = 0;
        uint last_index_bit = 1;
        while (mask > 0) {
            uint curr_bit = mask & 1u;
            uint active_bit = active_bit_mask & 1u;
            if (curr_bit > 0) {
                index |= last_index_bit;
            }
            if (active_bit > 0) {
                last_index_bit <<= 1;
            }
            mask >>= 1;
            active_bit_mask >>= 1;
        }
        return index;
    }

    bool do_xor(uint mask) {
        uint cnt = 0;
        while (mask > 0) {
            uint bit = mask & 1u;
            cnt ^= bit;
            mask >>= 1;
        }
        return cnt > 0;
    }

    void build(MSF& msf) {
        int n = msf.msf_g.n;
        int k = msf.msf_g.k;

        graph.resize(n + 1);
        std::vector<uint> active_bit_masks(n + 1);
        graph[0] = std::vector<Node>(1, Node());
        active_bit_masks[0] = 0;

        int line_ind = 0;
        for (int j = 0; j < n; j++) {
            bool line_activated = line_ind < k && msf.msf_g[line_ind][j];
            int active_lines_cnt = 0;
            uint active_bit_mask = 0;
            uint column = 0;

            uint deg = 1;
            for (int i = 0; i < k; i++, deg <<= 1) {
                if ((msf.start_indexes[i] <= j && msf.end_indexes[i] > j)
                    || (msf.start_indexes[i] == j && msf.end_indexes[i] == j)) {
                    active_bit_mask |= deg;
                    active_lines_cnt++;
                }
                if (msf.msf_g[i][j]) {
                    column |= deg;
                }
            }

            active_bit_masks[j + 1] = active_bit_mask;
            graph[j + 1] = std::vector<Node>(1u << active_lines_cnt);

            for (size_t index = 0; index < graph[j].size(); index++) {
                uint mask = index_to_mask(index, active_bit_masks[j]);
                uint to = mask & active_bit_mask;
                uint c = do_xor(mask & column);
                uint to_index = mask_to_index(to, active_bit_mask);
                graph[j + 1][to_index].edges.emplace_back(index, c);

                if (!line_activated) continue;

                to |= (1u << line_ind);
                mask |= (1u << line_ind);
                c = do_xor(mask & column);
                to_index = mask_to_index(to, active_bit_mask);
                graph[j + 1][to_index].edges.emplace_back(index, c);
            }
            if (line_activated) {
                line_ind++;
            }
        }
    }
}

/*
 * Кодирование заданного двоичного информационного вектора в заданном линейном коде
 */
namespace Encoder {
    BinaryVector encode(Matrix& g, BinaryVector& binary_vector) {
        std::vector<bool> c = std::vector<bool>(g.n, false);
        for (int j = 0; j < g.n; j++) {
            for (int i = 0; i < g.k; i++) {
                c[j] = c[j] ^ (binary_vector[i] & g[i][j]);
            }
        }
        return BinaryVector(c);
    }
}

/*
 * Декодирование заданного вектора по решетке по критерию максимума правдоподобия в канале с АБГШ
 */
namespace Decoder {
    double get_dist(int c, double y) {
        return c == 0 ? y : -y;
    }

    BinaryVector decode(std::vector<double>& y) {
        size_t layers = Trellis::graph.size();
        std::vector<std::vector<double>> d(layers);
        std::vector<std::vector<Edge>> prev(layers);

        d[0].assign(1, 0.0);
        for (int j = 1; j < layers; j++) {
            d[j].resize(Trellis::graph[j].size(), -1e6);
            prev[j].resize(Trellis::graph[j].size());
            for (int index = 0; index < Trellis::graph[j].size(); index++) {
                for (Edge& edge : Trellis::graph[j][index].edges) {
                    double curr_dist = d[j - 1][edge.from] + get_dist(edge.c, y[j - 1]);
                    if (d[j][index] < curr_dist) {
                        d[j][index] = curr_dist;
                        prev[j][index] = edge;
                    }
                }
            }
        }

        std::vector<bool> c(layers - 1);
        uint curr_ind = 0;
        for (size_t i = layers - 1; i > 0; i--) {
            Edge edge = prev[i][curr_ind];
            c[i - 1] = edge.c;
            curr_ind = edge.from;
        }
        return BinaryVector(c);
    }
}

/*
 * Симуляция: последовательная генерация информационного вектора,
 * его кодирование в заданном линейном коде,
 * передача по каналу с двоичной амплитудно-импульсной модуляцией и АБГШ,
 * декодирование по критерию максимума правдоподобия
 * и проверка наличия ошибок декодирования
 */
double simulate(Matrix& g,
                double noise_level, int max_iterations, int max_errors,
                int n, int k) {
    double sigma_squared = (double(n) / (2 * k)) * pow(10, -noise_level / 10);
    double sigma = sqrt(sigma_squared);

    int errors = 0;
    int iterations = 1;
    for (; iterations <= max_iterations; iterations++) {
        std::vector<bool> inform_vector(k);
        for (int j = 0; j < k; j++) {
            inform_vector[j] = RandomGenerator::nextBit();
        }
        BinaryVector binary = BinaryVector(inform_vector);

        BinaryVector code_word = Encoder::encode(g, binary);

        std::vector<double> y(n);
        for (int i = 0; i < n; i++) {
            y[i] = code_word[i] == 0 ? 1 : -1;
            y[i] += RandomGenerator::nextEta(sigma);
        }

        BinaryVector decoded_code_word = Decoder::decode(y);

        for (int i = 0; i < n; i++) {
            if (decoded_code_word[i] != code_word[i]) {
                errors++;
                break;
            }
        }

        if (errors == max_errors) {
            break;
        }
    }
    return double(errors) / iterations;
}

int main() {
    freopen("input.txt", "r", stdin);
    freopen("output.txt", "w", stdout);
    std::ios_base::sync_with_stdio(false);
    std::cin.tie(nullptr);
    std::cout.tie(nullptr);

    int n, k;
    std::cin >> n >> k;

    Matrix g(k, n);
    std::cin >> g;

    MSF msf = MSF::to_minimal_span_form(g);
    Trellis::build(msf);

    for (int i = 0; i <= n; i++) {
        std::cout << Trellis::graph[i].size() << " ";
    }
    std::cout << "\n";

    std::string command;
    while (std::cin >> command) {
        if (command == "Encode") {
            BinaryVector x(k);
            std::cin >> x;
            BinaryVector encoded = Encoder::encode(g, x);
            std::cout << encoded << "\n";
        } else if (command == "Decode") {
            std::vector<double> y(n);
            for (int i = 0; i < n; i++) {
                std::cin >> y[i];
            }
            BinaryVector decoded = Decoder::decode(y);
            std::cout << decoded << "\n";
        } else if (command == "Simulate") {
            double noise_level;
            int max_iterations, max_errors;
            std::cin >> noise_level >> max_iterations >> max_errors;
            double res = simulate(g, noise_level, max_iterations, max_errors, n, k);
            std::cout << res << "\n";
        }
    }
    return 0;
}
