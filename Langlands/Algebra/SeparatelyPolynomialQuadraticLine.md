# Separately polynomial functions on `ℕ³` along quadratic lines

Lean module: `Langlands.Algebra.SeparatelyPolynomialQuadraticLine`, namespace
`Langlands.Algebra.SeparatelyPolynomial`. Author: Worker 195.

This module is pure algebra over `ℚ`. It is a helper for the Euler-coefficient degree on
endomorphisms of abelian varieties (module
`Langlands.AbelianScheme.EndomorphismEulerDegree`). There it shows that the degree is
polynomial of degree at most `2 * g` along lines.

## Provenance

These are elementary facts about polynomial interpolation. They are not taken from a
particular source. Lagrange interpolation comes from Mathlib (`Lagrange.basis`,
`Lagrange.eq_interpolate`). The final theorem was formulated for this project to replace a
multivariable Euler-polynomial argument. Classically one would say that `χ(L₁^{x} ⊗ L₂^{y} ⊗ L₃^{z})`
is a polynomial of total degree at most `g` (Snapper). Here only polynomiality in each variable
separately, with degree at most `g`, is used. The resulting bound `2 * g` uses only
the degree in `m` and the shape of the substitution.

## Declarations

### `lagrangeWeight D i s` (definition)

The coefficient of `X ^ i` in the Lagrange basis polynomial at node `s` for the nodes
`0, 1, …, D` (as rationals).

### `coeff_eq_sum_lagrangeWeight`

If `p.natDegree ≤ D`, then
`p.coeff i = ∑ s ∈ range (D + 1), lagrangeWeight D i s * p.eval s`.
Proof: rewrite `p` as its Lagrange interpolant on the `D + 1` distinct nodes
(`Lagrange.eq_interpolate`, applicable because `degree p < D + 1`). Then take coefficients of the sum
`∑ C (p.eval s) * basis s`.

### `eq_sum_of_eval`

If `f x = p.eval x` for all natural `x` and `p.natDegree ≤ D`, then
`f x = ∑ i ≤ D, x ^ i * ∑ s ≤ D, lagrangeWeight D i s * f s`. Proof: expand `p.eval x` over
`range (D + 1)` (`eval_eq_sum_range'`), apply `coeff_eq_sum_lagrangeWeight` to each
coefficient, and replace `p.eval s` by `f s`.

### `exists_eval_sum`

A finite rational linear combination `∑ j ∈ t, c j * f j x` of functions `ℕ → ℚ`, each given
by a polynomial of natural degree at most `D`, is given by such a polynomial, namely
`∑ C (c j) * P j`.

### `exists_eq_sum_monomial`

**Statement.** Let `G : ℕ → ℕ → ℕ → ℚ` be polynomial of natural degree at most `D` in each
variable when the other two are fixed (hypotheses `hx`, `hy`, `hz`). Then there are
coefficients `c i j l` with
`G x y z = ∑ i, j, l ≤ D, c i j l * x ^ i * y ^ j * z ^ l` for all natural `x, y, z`.

**Proof.** Put `w = lagrangeWeight D` and define in turn
`a i y z = ∑ s w i s * G s y z`, `b i j z = ∑ t w j t * a i t z`,
`c i j l = ∑ r w l r * b i j r`. Then:

1. `G x y z = ∑ i x ^ i * a i y z` by `eq_sum_of_eval` in `x` (from `hx`).
2. `a i · z` is a combination of the functions `G s · z`. By `hy` and `exists_eval_sum` it is
   polynomial of degree at most `D` in `y`. So `a i y z = ∑ j y ^ j * b i j z` by
   `eq_sum_of_eval`.
3. Likewise `a i t ·`, and hence `b i j ·`, is polynomial of degree at most `D` in `z` (from
   `hz`), so `b i j z = ∑ l z ^ l * c i j l`.

Substituting and distributing the sums gives the claim (`ring` on each term).

### `exists_coeff_eq_eval_of_quadraticLine`

**Statement.** Let `G` be as above (separately polynomial of degree at most `D`). Let
`E : ℕ → ℚ[X]` be a family of polynomials with
`(E n).eval m = G (m * C(n, 2)) (m * n) m` for all natural `n, m`. Then for every `g` there is
`R : ℚ[X]` with `R.natDegree ≤ 2 * g` and `(E n).coeff g = R.eval n` for all natural `n`.

**Proof.**

1. Expand `G` into monomials with `exists_eq_sum_monomial`.
2. Let `A = (1/2) X (X - 1)`, of natural degree at most `2`, with `A.eval n = C(n, 2)`.
3. For each `n`, `E n` equals the polynomial
   `T n = ∑ i, j, l C (c i j l * C(n,2) ^ i * n ^ j) * X ^ (i + j + l)`. The two polynomials
   agree at every natural number, hence at infinitely many points
   (`eq_of_infinite_eval_eq`).
4. Take `R = ∑ i, j, l C (if g = i + j + l then c i j l else 0) * A ^ i * X ^ j`. Each nonzero
   term has natural degree at most `2 i + j ≤ 2 (i + j + l) = 2 g`. The `g`-th coefficient
   of `T n` is `∑_{i+j+l=g} c i j l * C(n,2) ^ i * n ^ j = R.eval n`.
