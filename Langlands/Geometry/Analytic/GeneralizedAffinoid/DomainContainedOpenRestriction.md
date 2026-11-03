# Intrinsic and ambient restrictions on contained ordinary opens

Author: Worker 36.

This internal construction compares actual restrictions over ordinary opens
contained in a full affinoid domain. Its parameters are a complete ultrametric
normed field `K`, an actual presented affinoid algebra `A` over `K`, and
`d : Domain K A`. Thus `d.algebra` is an actual presented quotient algebra and
`d.baseMap` is its bounded structural homomorphism, with the full affinoid-test
representation property already built into `Domain`.

For any ordinary ambient open `U` with `U ⊆ d.locus`, the entire intrinsic inverse
image of `U` is isomorphic to the ambient restriction over `U`, both as an
algebra-sheafed space and as a locally ringed space. The entire locus `d.locus`
need not be open. In particular this applies to its interior. No nontrivial
valuation, reducedness, nonzero quotient, or nonempty spectrum is assumed.

## The actual restricted spectral map

`preimageOpen d U` is the ordinary open inverse image of `U` under
`openSpectrumMap d.baseMap`. `spectrumMapOnOpen d U` is the inclusion of that open
subspace followed by the original spectral map.

`spectrumMapOnOpen_range` proves that its image is exactly `U` under the stated
containment hypothesis. One direction uses membership in the full inverse image;
the other uses the exact-image clause of the represented domain to obtain an
intrinsic preimage of each point of `U`.

`spectrumMapOnOpen_isOpenEmbedding` combines the already proved embedding of the
full-domain structural spectrum map with the open-subspace embedding. Its range
is open because it is exactly `U`. This argument does not assert that the
original map on the entire intrinsic spectrum is an open embedding.

## Algebra sheaves and the comparison

`algebraSheafedSpaceMapOnOpen d U` is the composite

```text
(algebraSheafedSpace K d.algebra)|preimageOpen(d,U)
  → algebraSheafedSpace K d.algebra
  → algebraSheafedSpace K A.
```

The first arrow is Mathlib's canonical `ofRestrict`; the second is the original
`algebraSheafedSpaceMap d.baseMap`. Thus its section component on an ambient open
`W` is the original bounded-map pullback followed by the canonical intrinsic
restriction component.

For every `W ≤ U`, `algebraSheafedSpaceMapOnOpen_app_isIso` proves that this
actual component is an isomorphism. The original pullback component is invertible
by `openAlgebraPresheafMap_app_isIso` from `DomainOpenImmersion`, since
`W ⊆ d.locus`.
The second component is invertible by Mathlib's
`PresheafedSpace.IsOpenImmersion.isIso_of_subset` for the canonical restriction
inclusion, since the inverse image of `W` is contained in the inverse image of
`U`. Their composition is therefore invertible.

`algebraSheafedSpaceMapOnOpen_isOpenImmersion` proves that the composite is an
open immersion: the base is the embedding just constructed, and every image
open is contained in `U`, so the preceding component result applies.

`algebraSheafedSpaceContainedOpenIso d U hU` has source the intrinsic algebra
sheaf restricted to the full inverse image of `U` and target the ambient algebra
sheaf restricted to the ordinary open subtype `U`. The two maps into the
ambient sheafed space are open immersions with equal range `U`. Mathlib's
`PresheafedSpace.IsOpenImmersion.isoOfRangeEq` constructs their comparison,
and `SheafedSpace.isoMk` lifts it to sheafed spaces. The forward comparison is
Mathlib's open-immersion lift through the ambient restriction inclusion; its
inverse is the lift in the other direction. The lift factorization and
uniqueness give the inverse identities.

`algebraSheafedSpaceContainedOpenIso_hom_ofRestrict` states the actual-morphism
factorization: composing the comparison with the ambient `ofRestrict` recovers
`algebraSheafedSpaceMapOnOpen d U`. Its proof is Mathlib's `lift_fac`, lifted
through the induced category. In particular the comparison retains the original
structural morphism and its action on actual quotient-valued sections.

## Ring sheaves and locally ringed spaces

`ringSheafedSpaceMapOnOpen` is the analogous restriction composite for the
existing ring-sheaf morphism. Its section component is definitionally the scalar
forgetting of the algebra-sheaf component above. The functor from `CommAlgCat K`
to `CommRingCat` preserves isomorphisms, proving
`ringSheafedSpaceMapOnOpen_app_isIso`. The same exact-image argument then gives
`ringSheafedSpaceMapOnOpen_isOpenImmersion`.

`ringSheafedSpaceContainedOpenIso` applies the same equal-range construction to
these ring sheaves. Its `_hom_ofRestrict` theorem factors the actual ring-sheaf
restriction composite.

`locallyRingedSpaceMapOnOpen` composes the canonical locally ringed-space
restriction inclusion with the original `locallyRingedSpaceMap d.baseMap`.
Both are existing morphisms with locality proved on genuine ordinary-open stalks.
Its underlying ring-sheaf morphism is the composite just treated, which proves
`locallyRingedSpaceMapOnOpen_isOpenImmersion`.

`locallyRingedSpaceContainedOpenIso` lifts the constructed ring-sheaf isomorphism
using Mathlib's `LocallyRingedSpace.isoOfSheafedSpaceIso`. The inverse is local
because an isomorphism of ring stalks is a local homomorphism. The theorem
`locallyRingedSpaceContainedOpenIso_hom_ofRestrict` proves its factorization over
the original ambient locally ringed space, by faithfulness of the forgetful
functor and the ring-sheaf factorization.

`locallyRingedSpaceInteriorIso` specializes this construction to the ordinary
open `interior d.locus`, using `interior_subset`. Its source is the intrinsic
restriction to the full preimage of that interior; its target is the ambient
restriction to the interior itself.

## Provenance and scope

This is a derived internal construction from `DomainOpenImmersion`,
`RationalOpenMorphism`, the proved full-domain spectral embedding, and Mathlib's
restriction, equal-image open-immersion, and locally ringed-space isomorphism
APIs. It adds no original-literature assertion. The explicit range argument and
the invertibility of the original sheaf components supply the hypotheses of
those APIs; no comparison object is assumed.

The result concerns ordinary opens contained in a full domain. It does not
identify the intrinsic sheaf of an arbitrary closed domain with an ordinary
inverse-image sheaf on the whole closed locus, including its boundary. General
analytic atlases, analytic etale and quasi-etale sites, equivariant sites,
distinguished domains and Harris towers remain separate construction obligations.
