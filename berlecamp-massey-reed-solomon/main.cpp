#include <iostream>
#include <vector>
#include <algorithm>
#include <random>

int64_t n, delta, k;
std::vector<uint64_t> g;
std::vector<uint64_t> deg_to_element;
std::vector<uint64_t> mask_to_deg;

void print(std::vector<uint64_t>& p, size_t size = n) {
    for (size_t i = 0; i < std::min(p.size(), size); i++) {
        std::cout << p[i] << " ";
    }
    for (size_t i = p.size(); i < size; i++) {
        std::cout << 0 << " ";
    }
    std::cout << "\n";
}

namespace GF {
    /*
     * Предподсчитываем битовые маски элементов из GF(2^m) через примитивный многочлен
     * */
    void init(uint64_t primitive_polynom) {
        uint64_t size = n + 1;
        deg_to_element.resize(2 * size);
        mask_to_deg.resize(size);
        uint64_t curr = 1;
        uint64_t deg = n + 1;
        for (int i = 0; i < n; i++) {
            deg_to_element[i] = curr;
            mask_to_deg[curr] = i;
            curr <<= 1;
            if (curr >= deg) {
                curr ^= primitive_polynom;
            }
        }
        for (uint64_t i = n; i < 2 * size; i++) {
            deg_to_element[i] = deg_to_element[i - n];
        }
    }

    /*
     * Умножение в GF(2^m)
     */
    uint64_t mul(uint64_t first, uint64_t second) {
        if (first == 0 || second == 0) {
            return 0;
        }
        return deg_to_element[mask_to_deg[first] + mask_to_deg[second]];
    }

    uint64_t mul_with_degs(uint64_t deg1, uint64_t deg2) {
        return deg_to_element[deg1 + deg2];
    }

    /*
     * Деление в GF(2^m)
     */
    uint64_t div(uint64_t first, uint64_t second) {
        uint64_t deg1 = mask_to_deg[first];
        uint64_t deg2 = mask_to_deg[second];
        return deg_to_element[n - deg2 + deg1];
    }
}

namespace Polynoms {
    /*
     * Вычисление значения многочлена в точке в GF(2^m) при помощи схемы Горнера
     */
    uint64_t value_at(std::vector<uint64_t> &polynom, uint64_t x_deg) {
        uint64_t value = polynom[polynom.size() - 1];
        for (int i = 1; i < polynom.size(); i++) {
            if (value != 0) {
                value = GF::mul_with_degs(x_deg, mask_to_deg[value]);
            }
            value ^= polynom[polynom.size() - 1 - i];
        }
        return value;
    }

    /*
     * Вычисление степени многочлена
     */
    int calc_deg(std::vector<uint64_t> &polynom) {
        int deg = polynom.size() - 1;
        while (deg >= 0 && polynom[deg] == 0) {
            deg--;
        }
        return deg;
    }

    /*
     * Деление многочленов в GF(2^m)
     */
    std::vector<uint64_t> polynom_div(std::vector<uint64_t> &first, std::vector<uint64_t> &second) {
        int first_deg = calc_deg(first);
        int second_deg = calc_deg(second);

        if (first_deg == -1) {
            return first;
        }

        std::vector<uint64_t> rem = first;
        while (first_deg >= second_deg) {
            uint64_t curr_value = GF::div(rem[first_deg], second[second_deg]);

            for (int i = 0; i <= second_deg; i++) {
                rem[i + first_deg - second_deg] ^= GF::mul(curr_value, second[i]);
            }
            while (first_deg >= 0 && rem[first_deg] == 0) {
                first_deg--;
            }
        }

        return rem;
    }
}

namespace Encoder {
    /*
     * Систематическое кодирование информационного вектора
     */
    void encode(std::vector<uint64_t>& input) {
        std::vector<uint64_t> rem = Polynoms::polynom_div(input, g);
        for (int i = 0; i < rem.size(); i++) {
            input[i] ^= rem[i];
        }
    }
}

namespace Decoder {
    /*
     * Декодирование при помощи алгоритма Берлекэмпа-Месси
     */
    void decode(std::vector<uint64_t>& y) {
        std::vector<uint64_t> syndrome(delta - 1, 0);

        for (int i = 0; i < delta - 1; i++) {
            syndrome[i] = Polynoms::value_at(y, i + 1);
        }

        int s_deg = Polynoms::calc_deg(syndrome);
        if (s_deg == -1) {
            return;
        }

        std::vector<uint64_t> locator(delta, 0);
        std::vector<uint64_t> b(delta, 0);

        locator[0] = 1;
        int l = 0;
        b[0] = 1;

        for (int r = 0; r < delta - 1; r++) {
            uint64_t value = 0;
            for (int j = 0; j <= l; j++) {
                value ^= GF::mul(locator[j], syndrome[r - j]);
            }

            for (int i = b.size() - 1; i > 0; i--) {
                b[i] = b[i - 1];
            }
            b[0] = 0;

            if (value != 0) {
                uint64_t value_deg = mask_to_deg[value];
                std::vector<uint64_t> old_b(delta, 0);
                for (int i = 0; i < b.size(); i++) {
                    old_b[i] = b[i];
                }

                if (2 * l <= r) {
                    for (int i = 0; i < locator.size(); i++) {
                        b[i] = GF::mul(locator[i], deg_to_element[n - value_deg]);
                    }
                    l = r + 1 - l;
                }

                for (int i = 0; i < old_b.size(); i++) {
                    locator[i] ^= GF::mul(value, old_b[i]);
                }
            }
        }

        std::vector<uint64_t> inverted_errors(l, 0);
        int ind = 0;
        for (uint64_t i = 0; i < n; i++) {
            if (Polynoms::value_at(locator, i) == 0) {
                inverted_errors[ind] = i;
                ind++;
            }
        }

        std::vector<uint64_t> gamma(delta, 0);
        for (int i = 0; i <= l; i++) {
            if (locator[i] == 0) continue;
            for (int j = 0; (j <= s_deg) && ((i + j) < delta - 1); j++) {
                gamma[i + j] ^= GF::mul(locator[i], syndrome[j]);
            }
        }

        for (int i = 0; i < ind; i++) {
            uint64_t inverted_deg = inverted_errors[i];
            uint64_t gamma_value = Polynoms::value_at(gamma, inverted_deg);
            if (gamma_value == 0) continue;

            uint64_t left = GF::mul(deg_to_element[inverted_deg], gamma_value);
            uint64_t right = 1;
            for (int j = 0; j < ind; j++) {
                if (i == j) continue;
                uint64_t product = GF::mul_with_degs(inverted_deg, n - inverted_errors[j]);
                uint64_t sm = product ^ 1u;
                right = GF::mul(right, sm);
            }
            y[(n - inverted_deg) % n] ^= GF::div(left, right);
        }
    }
}

/*
 * Симуляция: последовательно генерируем информационный вектор,
 * производим его систематическое кодирование
 * и декодирование при помощи алгоритма Берлекэмпа-Месси,
 * проверяем наличие ошибок декодирования.
 */
double simulate(
        double p, int max_iterations, int max_errors) {
    std::mt19937 get_random((std::random_device()) ());
    std::uniform_int_distribution<int> inform_distribution(0, n);
    std::uniform_int_distribution<int> symbol_distribution(1, n);
    std::uniform_real_distribution<> error_distribution(0, 1);

    std::vector<uint64_t> y(n);
    int errors = 0;
    int iterations = 1;

    for (; iterations <= max_iterations && errors < max_errors; iterations++) {
        std::vector<uint64_t> code_word(n, 0);
        for (int j = 0; j < k; j++) {
            code_word[j + delta - 1] = inform_distribution(get_random);
        }

        Encoder::encode(code_word);

        for (int i = 0; i < n; i++) {
            y[i] = code_word[i];
            double prob = error_distribution(get_random);
            if (prob < p) {
                y[i] ^= symbol_distribution(get_random);
            }
        }

        Decoder::decode(y);

        for (int i = 0; i < n; i++) {
            if (y[i] != code_word[i]) {
                errors++;
                break;
            }
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

    uint64_t primitive;
    std::cin >> n >> primitive >> delta;

    GF::init(primitive);

    k = n - delta + 1;

    std::cout << k << "\n";

    g.assign(delta, 0);
    g[0] = 1;

    for (int alpha_deg = 1; alpha_deg < delta; alpha_deg++) {
        std::vector<uint64_t> curr_g(alpha_deg);
        for (int j = 0; j < alpha_deg; j++) {
            curr_g[j] = g[j];
        }
        g[0] = 0;
        for (int j = 1; j <= alpha_deg; j++) {
            g[j] = curr_g[j - 1];
        }

        for (int j = 0; j < alpha_deg; j++) {
            g[j] ^= GF::mul(deg_to_element[alpha_deg], curr_g[j]);
        }
    }

    print(g, delta);

    std::vector<uint64_t> x(n);
    std::vector<uint64_t> v(n);
    std::string command;
    while (std::cin >> command) {
        if (command == "Encode") {
            for (int i = 0; i < k; i++) {
                std::cin >> x[i + delta - 1];
            }
            Encoder::encode(x);
            print(x);
        } else if (command == "Decode") {
            for (int i = 0; i < n; i++) {
                std::cin >> v[i];
            }
            Decoder::decode(v);
            print(v);
        } else if (command == "Simulate") {
            double noise_level;
            int max_iterations, max_errors;
            std::cin >> noise_level >> max_iterations >> max_errors;
            double res = simulate(noise_level, max_iterations, max_errors);
            std::cout << res << "\n";
        }
    }
    return 0;
}
