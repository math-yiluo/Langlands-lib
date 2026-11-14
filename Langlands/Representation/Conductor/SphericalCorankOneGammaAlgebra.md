# Rational-function algebra for the spherical corank-one functional equation

Module `Langlands.Representation.Conductor.SphericalCorankOneGammaAlgebra`, namespace
`Langlands.Conductor.SphericalCorankOne`. It is an internal helper for the proof of
`Langlands.Conductor.SphericalCorankOneFunctionalEquationStatement`. It states only identities
in `RationalFunctions = RatFunc ℂ` and one implication between two published functional-equation
predicates. No representation or integral occurs.

Notation: `rationalGammaExpression δ c m P P̃` is the published explicit gamma factor
`c X^m · P(X) / P̃(δ/X)` (`Langlands.RankinSelberg`). `rationalRescale z` is the published
`ℂ`-algebra map `X ↦ zX`.

## Statements

- `rationalRescale_rationalGammaExpression δ c z m P Pdual`: rescaling the gamma expression by
  `X ↦ zX` gives the gamma expression with constant `c z^m`, the same exponent `m`, the numerator
  polynomial `P(zX)` and the dual polynomial `P̃(z⁻¹X)`. That is, `P̃(δ/(zX))` is written as the
  polynomial `P̃(z⁻¹ ·)` evaluated at `δ/X`.
- `rationalGammaExpression_prod δ P PD c a`: over a finite index type, the gamma expression with
  constant `∏ c_i`, exponent `∑ a_i` and polynomials `∏ P_i`, `∏ PD_i` is the product of the
  individual gamma expressions.
- `prod_rationalRescale_rationalGammaExpression δ c m P Pdual x`: for `x : Fin (n+1) → ℂˣ`, the
  product over `i` of the rescalings by `x_i` of `c X^m P(X)/P̃(δ/X)` is the gamma expression with
  constant `c^(n+1) (∏ x_i)^m`, exponent `(n+1) m`, numerator `∏ P(x_i X)` and dual polynomial
  `∏ P̃(x_i⁻¹ X)`.
- `normalizedFunctionalEquation_of_gammaFunctionalEquation`: let `1 < q`, `δ = q⁻¹` and `ζ^e = 1`,
  and let `P̃ ≠ 0`. Suppose `R`, `R̃` satisfy the published
  `GammaFunctionalEquation q ζ e (rationalGammaExpression δ c m P P̃) R R̃`. Then they satisfy
  `NormalizedFunctionalEquation q P P̃ 1 c 0 m R R̃`, with sign `1` (exponent `0`) and epsilon
  monomial `c X^m`.

## Proofs

- Rescaling: unfold the gamma expression and push `rationalRescale` through quotient, product,
  `algebraMap` and `aeval`. The monomial part is `ring` after `zpow` is distributed. The
  reflected part is `field_simp` after evaluating `reflectedVariable δ = δ/X` under the rescaling.
- Product: first prove by `Finset` induction that `X^(∑ a_i) = ∏ X^(a_i)`. Then `simp` with
  `map_prod`, `Finset.prod_div_distrib` and `Finset.prod_mul_distrib`.
- Product of rescalings: rewrite each factor with the rescaling lemma and fold with the product
  lemma. The constant and the exponent are then `Finset.prod_const`/`Finset.prod_zpow` and
  `Finset.sum_const` over `Fin (n+1)`.
- Normalization: the published `rational_identity_of_gammaFunctionalEquation` gives the rational
  identity `subst δ R̃ = ζ^e · G · R`. With `ζ^e = 1`, multiplying by `P̃` and clearing the
  denominator `P̃(δ/X)`, which is nonzero because `δ/X` is transcendental
  (`RationalReflection.variable_transcendental`), gives
  `subst δ (P̃ R̃) = c X^m (P R)`. The proof evaluates this at the spectral point `q^(-s)`. It uses
  the published regularity and evaluation lemmas of `RationalEvaluation`, together with
  `spectralPoint_one_sub`, which turns `δ/q^(-s)` into `q^(-(1-s))`. Unfolding
  `epsilonMonomial` then gives the normalized equation pointwise.

## Provenance

Internal algebra for assembling JPSS 1981, (4.2), display (3), in the form stated by the target.
It has no counterpart in the literature beyond the elementary identities above.

The finite-product identity reuses `Langlands.RankinSelberg.TemperedLFactorGamma.rationalGammaExpression_prod` from [RationalGammaExpressionProduct](../RankinSelberg/RationalGammaExpressionProduct.md).
