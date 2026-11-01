# A relative integral action locus from a represented endomorphism presheaf

For an actual abelian scheme `B` over a scheme `S`, a ring `O` with a supplied
finite integer basis, and a supplied object `E` over `S`, this module constructs
an actual scheme over `S` classifying integral `O`-actions on the pullbacks of
`B`. The construction is conditional on two explicit inputs:

- A natural isomorphism `e` from the published relative endomorphism presheaf
  of `B` to the restricted Yoneda presheaf of `E`, on the full category of all
  locally noetherian schemes over `S`.
- Local noetherianness of the actual finite product `E^I` in `Over S`.

The second input is kept explicit. Arbitrary locally noetherian schemes over a
locally noetherian base need not have locally noetherian fibre products.
The module makes no such closure assertion and does not deduce this input from
local noetherianness of `E`.

`relativeIntegralActionLocus` specializes the equalizer in
`Langlands.Algebra.FiniteFreeRingHomLocus` to the canonical ring-valued relative
endomorphism presheaf. Forgetting that presheaf's ring structure gives exactly
the published relative-Hom presheaf used in the input `e`, by
`relativeEndRingFunctor_forget`. Thus the supplied comparison concerns actual
integral endomorphisms with the canonical restriction maps.

The product coordinates record the images of the integer basis. The two maps
to the finite equation product record the integer-linear sums and the unit
and ordered products from the ring's structure constants. Their actual
equalizer imposes precisely the unital ring homomorphism laws.
`relativeIntegralActionLocusInclusion` is the equalizer inclusion into `E^I`;
the module proves it is a monomorphism.

For every locally noetherian test scheme `T` over `S`,
`relativeIntegralActionLocusHomEquiv` identifies maps from `T` into this locus
with actual unital ring homomorphisms
`O → End(B ×_S T)`. Its basis evaluation theorem says that the image of each
basis vector is the corresponding projected morphism, decoded through
`e.inv`. The inverse reconstructs the action by the integer-linear
combination given by the supplied basis.

`relativeIntegralActionLocusIso` gives the natural isomorphism on the entire
same full test category, including every morphism over `S` between its objects.
It uses the canonical relative endomorphism restriction and the generic
equalizer comparison. The explicit `ULift` on the represented Hom presheaf
matches the common universe of the action functor. The scheme universe and
the universes of `I` and `O` remain independent.

This is an internal categorical construction from the supplied restricted
relative-End comparison, the explicit finite-power hypothesis, actual scheme
limits, and the published finite-basis ring-action equivalence. It introduces
no new literature assertion. The output has a natural action comparison on
locally noetherian tests; no local noetherianness, closed immersion, finite
type, smoothness or projectivity property of the locus is asserted here.
The module does not prove existence of the relative-End representative,
produce an integral model of a rational action, impose Rosati or determinant
conditions, or prove the normalized Harris CM representability statement.
