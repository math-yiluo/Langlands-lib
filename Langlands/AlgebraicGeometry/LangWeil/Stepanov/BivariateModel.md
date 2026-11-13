# From `MvPolynomial (Fin 2) F` to nested polynomials `F[X][Y]`

Author: Worker 5406. Internal helper for the proof of
`Langlands.AlgebraicGeometry.LangWeil.StepanovNormPolynomialsStatement`.

Provenance. These are routine bookkeeping facts with no counterpart in the literature. The
Library statement is phrased for `f : MvPolynomial (Fin 2) F` (variables `X 0`, `X 1`). The
Stepanov construction works with `fh : F[X][Y]`, the preimage of `f` under Mathlib's algebra
isomorphism `Polynomial.Bivariate.equivMvPolynomial F`, which sends `C X ↦ X 0` and `Y ↦ X 1`.
This file transfers the hypotheses and the fibre counts between the two forms.

## Results

- `single_add_single_eq_iff`, `eq_single_add_single`: exponents in `Fin 2 →₀ ℕ` are the pairs
  `single 0 i + single 1 j`.
- `coeff_equivMvPolynomial`, `coeff_coeff_equivMvPolynomial_symm`: the coefficient of `X^i Y^j`
  is the same on both sides. Proof by induction on monomials of `F[X][Y]`.
- `natDegree_equivMvPolynomial_symm`: `natDegree fh = degreeOf 1 f`.
- `natDegree_coeff_equivMvPolynomial_symm_le`: every coefficient `fh.coeff j ∈ F[X]` has degree
  `≤ degreeOf 0 f`.
- `equivMvPolynomial_symm_map`: the transfer commutes with base change, so
  `fh.map (mapRingHom φ)` corresponds to `MvPolynomial.map φ f`. Both statements reduce to the
  coefficient formula.
- `derivative_equivMvPolynomial_symm`: the `Y`-derivative of `fh` corresponds to `pderiv 1 f`
  (Mathlib's `pderiv_one_equivMvPolynomial`).
- `eval_equivMvPolynomial`: `f(x, y) = fh(x, Y)` evaluated at `y`, by extensionality of ring
  homomorphisms out of `F[X][Y]`.
- `map_evalRingHom_ne_zero_of_irreducible`: an irreducible `P ∈ F[X][Y]` of positive `Y`-degree
  does not vanish identically on the line `X = x`. Otherwise `X - x` divides every coefficient,
  so `C (X - x) ∣ P`. Irreducibility then forces either `X - x` to be a unit or the cofactor to
  be a unit, which makes `natDegree P = 0`.
- `card_zeros_eq_card_roots`: if `fh(x, Y) ≠ 0`, the number of `y ∈ F` with `f(x, y) = 0` is
  the number of distinct roots of `fh(x, Y)` in `F`.
- `BivariateModel` and `bivariateModel`: the package used in `NormPolynomials.lean`. Assume
  `f` is irreducible over `AlgebraicClosure F`, `pderiv 1 f ≠ 0` and `1 ≤ degreeOf 1 f`. Then
  - `fh` has degree `degreeOf 1 f` in `Y`, with coefficients of degree `≤ degreeOf 0 f`;
  - `fh` is irreducible over `F` and over `AlgebraicClosure F`;
  - `derivative fh ≠ 0`;
  - for every `x ∈ F`, `fh(x, Y) ≠ 0`, and the fibre count of `f` over `x` equals the number
    of distinct roots of `fh(x, Y)`.

  Irreducibility over `F` comes from the Library lemma `planeCurve_irreducible_of_absolute`.
  It and absolute irreducibility move across the ring isomorphism by
  `MulEquiv.irreducible_iff`.
