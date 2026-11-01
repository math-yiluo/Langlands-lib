# Whole-carrier local smooth restrictions of actual operator quotients

This internal construction uses the published continuous inclusion of
`FiniteLocalGL F n v` in `FiniteAdelicGL F n`. The number field
`F : Type uF` has arbitrary universe, the rank `n : ℕ` is unrestricted,
and the coefficient field is complex. The general finite-to-local functor
retains an independent carrier universe `uV`; actual form subspaces and
their module quotients have carrier universe `uF`.

`FiniteAdelicGL.localRestrictionFunctor` lifts Mathlib's representation
restriction functor to the published category of smooth representations.
The existing continuous local inclusion and continuous-pullback smoothness
theorem prove the lift's smoothness obligation. The representation is
literally composition with that inclusion, on the original carrier.
Morphisms retain their underlying complex-linear maps. Functoriality is
inherited from the actual functor lift, rather than separately assumed.
`localRestrictionClass` descends to the categorical isomorphism quotient:
the functor sends every supplied isomorphism to a genuine local
isomorphism, so its class is independent of the representative.

For an actual `OperatorRealization`, `localRepresentation` restricts its
finite action on its whole actual form carrier. Its smoothness is proved
by the same continuous restriction theorem, and
`localSmoothRepresentation` bundles that proof. `localFormEquiv` restricts
the existing faithful finite-image equivalence and identifies this local
action with the whole-carrier local restriction of its actual finite
image in forms. Its underlying map remains `finiteEquiv`.

For an actual `OperatorSubquotient`, `localSmoothRepresentation` bundles
the already published local action and smoothness proof. It is
definitionally the image of the published finite smooth object under the
new restriction functor. `localProjection` is the same actual canonical
numerator projection, now intertwining every local translation. It is
surjective, and its kernel as an underlying complex submodule is exactly
the original invariant denominator. The formula for local translation of
every projected representative is proved.

`OperatorSubquotient.Intertwiner.localRestriction` restricts every
supplied whole-operator intertwiner on the same quotient carriers.
`localRestrictionLinearMap` is complex-linear on the entire such Hom
space. Restriction is injective on that supplied space because the
underlying linear map is retained; it preserves identities and
composition. This does not assert that every local intertwiner commutes
with all global operators. Whole-action representation equivalences
restrict to genuine local representation equivalences, compatible with
the intertwiner restriction.

`OperatorSubquotient.IsoClass.localClass` factors through the existing
finite smooth class and the general finite-to-local class map. On every
actual presentation it is the smooth class of its whole-carrier local
restriction. `OperatorRealization.IsoClass.localClass` similarly uses the
existing finite image; `localFormEquiv` proves that on a representative
it equals the class of its original-carrier local action.
`toSubquotientLocalEquiv` is the actual zero-denominator projection
equivalence restricted locally. Its representative formula is proved.
The published finite-class compatibility of the zero-denominator bridge
then proves that the whole-action class embedding commutes with local
class forgetting.

Provenance is internal. All group maps, actual form images, module
quotients, quotient projections, finite smooth objects, zero-denominator
equivalences and class quotients are already published. The new functor
uses Mathlib's `Rep.resFunctor` and the full-subcategory lift; its smoothness
uses the project's continuous restriction theorem. The remaining map and
class constructions follow by restricting the supplied maps and descending
the resulting functor on genuine isomorphism classes. No new
identification with original literature is asserted.

These are restrictions on the whole carrier. They do not select local
tensor factors or assert local irreducibility, admissibility, a
restricted tensor decomposition, spectral existence or a local component
of an arbitrary class. No injectivity of the local class map is claimed.
No topology or function evaluation is assigned to general quotient
vectors. The module needs neither a CM field nor a character nor
compactness of the additive adele quotient.
