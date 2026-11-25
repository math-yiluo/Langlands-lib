# Exact inertia-field recovery for the descended inner model

This internal construction composes the existing exact finite inner
solution with actual coefficient-extension comparisons and the proved
equality between norm integers and the given valuation integers.
Its provenance is `normFiniteInnerModelIso`, `Iso.baseChangeCoefficients`,
`baseChangeTowerIso`, `givenIntegerModel` and `givenIntegerModelIso`.
No original-literature theorem is claimed. All objects have an arbitrary
common universe.

The inputs are exactly those of `finiteInnerIntegralSolution`: an actual
finite Galois arithmetically unramified field E/F inside the inertia fixed
field, a finite integral model N, a supplied smooth upstairs model P,
exact coefficient recovery of P from N, a function c upstairs, a finite
rational-point cocycle d recovering its values at selected lifts, and
both forward and inverse integral stability for P.

`finiteInnerInertiaGenericComparison` starts with the inverse canonical
generic tower comparison for the solution's own generic F-group. It
then applies the inertia-field base change of
`finiteInnerGenericComparison`, followed by the canonical
`finiteInertiaGenericIso` for the original group G. It is an actual
isomorphism between the inertia-field extensions of the descended
generic group and G. The construction preserves their distinction.

`normFiniteInnerInertiaModelIso` composes the inverse model coefficient
tower comparison, the coefficient extension of
`normFiniteInnerModelIso`, and the prescribed recovery of P. The
generic map of this composite is exactly
`finiteInnerInertiaGenericComparison` by construction, so the entire
original generic identification is retained.

`givenFiniteInnerModel` transports the descended norm-integer model
across the proved equality of integer subrings to the actual valuation
integers of F. `givenFiniteInnerModel_smooth` preserves the proved
smoothness. `givenFiniteInnerModelIso` uses the presentation transport
comparison to recover P under the actual unramified base change over
exactly the same generic map. Its compatible model isomorphism proves
`givenFiniteInnerModel_map_integralPoints`: that map carries the actual
integral-point image of the base-changed descended model onto the
actual integral-point image of P.

This module retains the supplied model and finite recovery hypotheses.
It supplies no all-automorphism inertia semilinearity, no residue
quotient or Frobenius identification, and no chamber conclusion.
