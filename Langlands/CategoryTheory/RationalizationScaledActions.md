# Exact scaled integral lifts of rational ring actions

This is an internal algebraic construction in any preadditive category. Let
`X` be an object, let `O` be a ring with a supplied finite integer basis, and
let `α : O →+* Rationalization.End X` be a unital rational action. The
construction produces a nonzero integer `n` and an integer-linear map
`g : O →ₗ[ℤ] CategoryTheory.End X` such that, for all `x,y ∈ O`,

* `ofEnd X (g x) = n • α x`;
* `g 1 = n • 1`;
* `g x * g y = n • g (x * y)`.

These are exact equalities of integral endomorphisms. No torsion-freeness of
the integral Hom groups is assumed. The lift is an integer-linear map with
scaled ring laws; it is not asserted to be a unital integral ring action.
The file constructs no new object or integral geometric model.

`ScaledIntegralLift` packages this data. The theorem
`nonempty_scaledIntegralLift` proves its existence, and `scaledIntegralLift`
chooses such a lift.

The proof uses `exists_common_integral_multiple` to clear the denominators
of the finitely many basis values. Integer-linear extension gives a first
lift `g₀` with common denominator `a`. Its unit and multiplication identities
hold after rationalization. `ofHom_eq_iff_exists_zsmul_eq` clears the integral
unit error by a nonzero integer `k`; `exists_common_zsmul_eq` clears all
basis-pair multiplication errors by one nonzero integer `l`. Taking
`t = k*l`, `g = t • g₀`, and `n = t*a` gives the exact scaled unit and
basis-pair multiplication laws. Equality of integer-bilinear maps extends
the multiplication law from basis pairs to arbitrary inputs.

This result is derived from the published rationalization and denominator
constructions and the integer-basis universal property. It supplies an
algebraic prerequisite for integralization arguments and does not assert
their geometric existence conclusions.
