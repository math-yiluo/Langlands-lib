# Original stalk maps over the interior of a full domain

Author: Worker 36.

This derived internal construction concerns an arbitrary complete ultrametric
normed field `K`, an actual presented affinoid algebra `A`, and a full represented
affinoid domain `d : Domain K A`. The domain has its actual presented algebra
`d.algebra`, bounded structural map `d.baseMap`, and original spectral map
`d.spectrumMap`.

The original algebra and ring stalk maps are isomorphisms at every intrinsic
point `y` whose image belongs to `interior d.locus`. The entire domain locus need
not be open. These are genuine ordinary-open stalks, defined by the existing
presheaf stalk colimits; the forward maps are precisely the maps already
constructed from `d.baseMap` in `RationalOpenMorphism`.

## A contained ordinary open

`openStalkMap_isIso_of_mem_open d U hU y hy` accepts an ambient ordinary open
`U`, containment `hU : U ⊆ d.locus`, and membership
`hy : d.spectrumMap y ∈ U`. It proves invertibility of the original
`openStalkMap d.baseMap y`.

The proof views `y` as a point `x` of the full intrinsic preimage
`preimageOpen d U`. The constructed
`algebraSheafedSpaceMapOnOpen d U` is the canonical intrinsic restriction
inclusion followed by the original algebra-sheaf morphism. The preceding
`DomainContainedOpenRestriction` construction proves that this composite is an
actual open immersion. Mathlib's open-immersion stalk theorem therefore proves
that its genuine stalk map at `x` is invertible.

Mathlib's `PresheafedSpace.stalkMap.comp` identifies that composite stalk map
with the original `openStalkMap d.baseMap y` followed by the stalk map of the
canonical intrinsic restriction inclusion. The latter is invertible by
Mathlib's `PresheafedSpace.ofRestrict_stalkMap_isIso`. Cancellation of that
invertible right factor proves the desired invertibility of the original map.
Thus the conclusion concerns the original unrestricted morphism at `y`, rather
than only the stalk map of a separately chosen restricted comparison.

`openRingStalkMap_isIso_of_mem_open` proves the same conclusion for
`openRingStalkMap d.baseMap y`. The published `openRingStalkMap_eq` identifies
this map with the scalar-forgotten algebra stalk map, conjugated by the
canonical genuine-stalk comparison isomorphisms `openStalkRingIso`. Scalar
forgetting preserves the algebra-map isomorphism just proved, and all three
factors are invertible.

## Interior specialization and bundled comparisons

`openStalkMap_isIso_of_mem_interior` and
`openRingStalkMap_isIso_of_mem_interior` specialize the preceding results to
the ordinary open `⟨interior d.locus, isOpen_interior⟩`, using
`interior_subset`.

`openInteriorStalkIso d y hy` is the resulting isomorphism from the ambient
ordinary-open algebra stalk at `d.spectrumMap y` to the intrinsic ordinary-open
algebra stalk at `y`. It is `asIso` of the original algebra stalk map, using the
proved invertibility. Its `_hom` theorem identifies its forward morphism with
`openStalkMap d.baseMap y` by definitional equality.

`openInteriorRingStalkIso` gives the corresponding isomorphism in `CommRingCat`
between the actual ring-presheaf stalks. Its `_hom` theorem identifies its
forward morphism with `openRingStalkMap d.baseMap y`. The latter is the ring-stalk
map of the original locally ringed-space morphism. The inverses and both inverse
identities come from `asIso` applied to these proved isomorphisms.

## Provenance and scope

This unit derives its results from the explicit contained-open open immersions
in `DomainContainedOpenRestriction`, the original bounded-map sheaf/stalk maps
and scalar-forgetting comparison in `RationalOpenMorphism`, and Mathlib's stalk
composition, restriction and isomorphism-cancellation APIs. It adds no new
original-literature assertion and assumes no comparison object or resulting
stalk isomorphism.

There is no nontrivial valuation, reducedness, nonzero quotient, or nonempty
spectrum hypothesis. The membership premise explicitly retains the interior
condition. No stalk comparison at boundary points, ordinary inverse-image sheaf
comparison on a closed domain's entire locus, unrestricted analytic atlas,
analytic etale or quasi-etale site, equivariant site, distinguished domain or
Harris tower construction is asserted here.
