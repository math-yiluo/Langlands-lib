# The canonical-dual enlarged product over supplied KP building data

Author: Worker 455.

This unit constructs the enlarged product over the same supplied
`B : ValuationBuildingData G`. The field has arbitrary universe `u`, either
characteristic, and the existing nonarchimedean-local-field instances. The
actual group scheme `G` has the affineness instance required by `B`; its
connected reductivity is part of `B`. No existence of such data is claimed.

## Construction and intrinsic laws

`B.EnlargedBuilding` is `B.ReducedBuilding × CentralFactor G`, and
`B.EnlargedApartment` is `B.Apartment × CentralFactor G`. Their actions are
the inherited product actions: the existing action on the reduced factor and
the actual negative rational-character translation of `KPCentralFactor`.
The apartment uses the existing action of `normalizerPoints B.i` on its first
factor and the subgroup restriction of the actual central action on its second.
`enlargedApartmentMap` is the reduced apartment map times the identity. Its
normalizer equivariance follows coordinatewise from the existing reduced
map's equivariance. The optional injectivity lemma explicitly assumes
injectivity of that same reduced map.

`enlargedApartmentImage` is the range of this map, and
`enlargedTranslatedApartment g` is its translate under the product action.
`enlargedTranslatedApartmentMap` has exactly that range. The translated
subset is `(g • B.apartmentImage) × univ`: the first coordinate follows the
existing reduced translated map, and the inverse action chooses a preimage
for any requested central coordinate. Taking `g = 1` gives the base case.

`enlargedProjection` is the first projection; `enlargedZeroSection` inserts
zero. The projection is equivariant and surjective and retracts the zero
section. The zero section is equivariant for the actual
`rationalCommonNormKernel G` subgroup, since this subgroup fixes every central
coordinate. `centralTranslate v` adds `v` to the second coordinate. Its zero
and addition laws are proved, it preserves projection and commutes with the
actual group action. Two enlarged points have equal projections exactly when
one is a central translate of the other; their difference supplies the vector.

`enlargedStabilizer` and `enlargedPointwiseFixer` are the actual full point
stabilizer and pointwise fixing subgroup for the product action. A group element
fixes a point exactly when it fixes the reduced coordinate and belongs to the
actual norm kernel. Thus the full stabilizer equals `B.compactStabilizer` at the
projection and equals `rationalCommonNormKernel G ⊓ B.fixer` there. It is
independent of the central coordinate. For a nonempty enlarged subset `Y`, its
pointwise fixer is the norm kernel intersected with `B.pointwiseFixer` of the
projection image. One point of `Y` detects norm-kernel membership; the converse
uses the central fixed-point criterion at each point. Projection of
`Ω × univ` is exactly `Ω`, giving the product formula when `Ω` is nonempty.
The empty enlarged subset has the whole group as pointwise fixer.

## Source, provenance and scope

The registered source is Kaletha–Prasad, *Bruhat–Tits Theory: A New Approach*
(2023), `kaletha-prasad-2023-bruhat-tits-new-approach`, SHA256
`05ad9a284a2577b34d1a270228b74dfb28f520561ae7772d8f38dddb78938732`,
§4.3, especially Definition 4.3.2 and Lemma 4.3.3, printed pp.178–179 /
PDF pp.209–210. The registered authors' corrections dated 1 November 2024,
`kaletha-prasad-2024-corrections`, SHA256
`23293f51e58d5ceecb91f834743f68058b98431797d2531142415d013fdf61ed`,
PDF p.25, supply the positive valuation convention; the central action retains
the source's negative sign. Corrections PDF pp.27–29 contain no §4.3 correction.
These passages were read directly while preparing this construction.

The canonical dual is an internal realization of the source's enlarged
construction. Its comparison with the real cocharacter space of an actual
split component is a separate conditional construction using the actual
restriction evaluation map. The intrinsic proofs here use product equality,
additive cancellation and the published reduced-building and actual norm-kernel
APIs. They assert subgroup identities, without compactness or openness. This
unit supplies no metric, full-torus splitting, bounded-set assertion, parahoric
comparison, derived-point equivariance, full corrected building predicate or
general building existence.
