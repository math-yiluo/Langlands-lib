# Arithmetic of pole orders at `s = 0`

This module proves elementary facts about the Library's
`lPolynomialPoleOrderAtZero P`, the multiplicity of `1` as a root of the
polynomial `P`. Since `L(s) = 1 / P(q^(-s))` and `q^(-s) = 1` at `s = 0`, this
is the order of the pole of `L(s)` at `s = 0`. Henniart 2002, Théorème 1.7(b),
compares such pole orders. The module states nothing about representations.

## Provenance

Derived. The results are standard properties of root multiplicities. The
specific polynomial `∏_(a ∈ A) (1 - a X)` is the form of the L-factor in
Jacquet, Piatetski-Shapiro and Shalika, *Rankin-Selberg convolutions* (1983),
Proposition (8.1)(ii), printed page 443, as stated in the Library's
`SupercuspidalEqualRankLFactorStatement`. That form is why the last lemma is
included.

## Contents

- `ne_zero_of_coeff_zero_eq_one`: a polynomial with constant coefficient `1` is
  nonzero. L-polynomials in the Library are normalized this way.
- `lPolynomialPoleOrderAtZero_mul`: for nonzero `P` and `Q`, the pole order of
  `P * Q` is the sum of the pole orders. This is `Polynomial.rootMultiplicity_mul`.
- `lPolynomialPoleOrderAtZero_prod`: the same for a finite product
  `∏ i ∈ s, P i` of nonzero polynomials. The proof is induction on the finset.
- `lPolynomialPoleOrderAtZero_prod_prod`: for finite index types `ι`, `κ` and
  polynomials `Q i j` with constant coefficient `1`, the pole order of
  `∏ i, ∏ j, Q i j` is `∑ i, ∑ j` of the pole orders. JPSS's formulas for
  L-factors of square-integrable and tempered representations are products of
  this shape.
- `lPolynomialPoleOrderAtZero_one_sub_C_mul_X`: the pole order of `1 - a X` is
  `1` if `a = 1` and `0` otherwise. For `a = 1` the polynomial is
  `(X - 1) · (-1)`. For `a ≠ 1`, `1` is not a root.
- `lPolynomialPoleOrderAtZero_prod_one_sub_C_mul_X`: for a finite set `A` of
  complex numbers, the pole order of `∏_(a ∈ A) (1 - a X)` is `1` if `1 ∈ A`
  and `0` otherwise. This follows by summing the previous lemma over `A`.
