# Derivations of polynomial rings shifting a weighted grading

Module `Langlands.Algebra.MvPolynomialDerivationGrading`, namespace
`Langlands.Algebra.MvPolynomialDerivationGrading`.

Throughout, `R` is a commutative ring and `wt : σ → ℤ` gives the variables integer weights;
`weightedHomogeneousComponent wt n` is Mathlib's component of weight `n`.

## Results

- `isWeightedHomogeneous_derivation_monomial`, `isWeightedHomogeneous_derivation`: if a
  derivation `D` sends each `X i` to a polynomial of weight `wt i + c`, it sends polynomials of
  weight `n` to polynomials of weight `n + c`. For monomials this is an induction on the exponent
  using the Leibniz rule and `Derivation.leibniz_pow`; Mathlib's
  `IsWeightedHomogeneous.induction_on` extends it to homogeneous polynomials.
- `weightedHomogeneousComponent_derivation`: for such `D`, the component of weight `n + c` of
  `D p` is `D` of the component of weight `n` of `p` (checked on monomials).
- `shiftPart wt D c` is the derivation sending `X i` to the component of weight `wt i + c` of
  `D (X i)` (`shiftPart_X`, `shiftPart_isWeightedHomogeneous`).
- `eq_shiftPart_add`: if every `D (X i)` has components only in weights `wt i - 1`, `wt i` and
  `wt i + 1`, then `D` is the sum of its three shift parts (two derivations agreeing on the
  variables are equal, `MvPolynomial.derivation_ext`).
- `eq_zero_of_derivations` (**lowest-component argument**). Let `s` be a polynomial whose
  monomials all satisfy a predicate `Q`, annihilated by every member of a family of derivations
  of the above kind. Suppose that every nonzero polynomial whose monomials satisfy `Q` is not
  annihilated by the weight-lowering part `shiftPart wt (D y) (-1)` of some member. Then
  `s = 0`. Indeed, if `s ≠ 0`, let `W` be the least weight of a monomial of `s` and `s₀` its
  component of weight `W`. The component of weight `W - 1` of `D y s = 0` is
  `shiftPart (D y) (-1) s₀`, because the components of `s` of weights `W - 1` and `W - 2` vanish.
  This contradicts the hypothesis applied to `s₀ ≠ 0`.

## Provenance

Internal lemmas about Mathlib's weighted homogeneous polynomials, used in
`Langlands.Algebra.LieCenterProjectionInjective` for the injectivity of the Harish-Chandra
projection.
