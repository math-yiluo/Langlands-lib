# Finite full-domain sites under bounded base equivalences

Let `K : Type u` be a complete ultrametric normed field, let `A` and `B`
be presented affinoid `K`-algebras with arbitrary positive polyradii, and
let `e : BoundedAlgEquiv K A B` be an actual bounded algebra equivalence.
This module constructs `Domain.transportBaseSheafEquivalence e T` between
the sheaf categories of the two finite full-domain sites. It also
identifies the actual stored algebra sheaves under this equivalence in
both directions. The coefficient category `T : Type v` has independent
morphism universe `w`; it needs no completeness or sheafification hypothesis.

## Actual site transport

The published `DomainBaseTransport` construction sends a full domain `U`
over `A` to the full domain over `B` with the same presented algebra,
structural map `U.baseMap.comp e.symm.toBoundedAlgHom`, and represented
locus `e.spectrumHomeomorph ⁻¹' U.locus`. It retains every actual bounded
restriction map. Its inverse uses `e.symm`, and its round-trip
isomorphisms have identity bounded restrictions.

`transportBaseFunctor_isCocontinuous` lifts every finite covering sieve.
For a covering sieve on `transportBase e U`, take its finite witness
`D i`, with arrows `f i`. Transport each `D i` and `f i` along `e.symm`
and compose with the inverse unit component at `U`. Mapping this new
arrow forward agrees, by uniqueness of full-domain arrows, with the
counit component followed by `f i`. Downward closure of the original
sieve therefore proves the required sieve membership. The published
`FiniteCover.familyCovers_transportBase_iff` transports its actual locus
coverage, and `transportBase_symm_locus` identifies the round-trip target
locus with `U.locus`. The supplied finite index is retained, including
when it is empty.

Applying the same construction to `e.symm` gives cocontinuity in the
other direction. Alias instances expose these properties for the
functor and inverse of `transportBaseEquivalence e`. Mathlib's
equivalence results then give the displayed dense-subsite instances
and construct `transportBaseSheafEquivalence` by `Equivalence.sheafCongr`.
No sheafness or descent output is assumed.

The entire underlying presheaf of its forward image is
`(transportBaseFunctor e.symm).op ⋙ F.obj`; the inverse image uses
`(transportBaseFunctor e).op ⋙ F.obj`. The two
`transportBaseSheafEquivalence_*_obj` equations record these formulas by
reflexivity.

## Stored algebra sheaf compatibility

`transportBase_boundedPresheaf` and `transportBase_algebraPresheaf`
identify the complete presheaves, including all objects and restriction
arrows, after precomposition with `(transportBaseFunctor e).op`.
Specializing these equations to `e.symm` also gives the equalities in
the other direction.

`transportBaseAlgebraSheafIso e` identifies the forward image of
`algebraSheaf K A` with `algebraSheaf K B`.
`inverseTransportBaseAlgebraSheafIso e` identifies the inverse image of
`algebraSheaf K B` with `algebraSheaf K A`. The underlying presheaves are
definitionally equal, so `ObjectProperty.isoMk _ (Iso.refl _)` lifts
their identity presheaf isomorphisms to sheaves.

The `*_hom_apply` and `*_inv_apply` equations show that both components
of each comparison are identity algebra maps on every original section.
The two `*AlgebraSheaf_map_apply` equations show that restriction remains
exactly `f.restriction a`. The forward structural-map formula identifies
the section coming from `a : A` with `U.baseMap (e a)` on each domain
`U` over `B`. The inverse formula identifies the section from `b : B`
with `U.baseMap (e.symm b)` on each domain over `A`. These equations
retain the actual supplied bounded base maps, rather than an arbitrary
algebra isomorphism.

## Provenance and scope

This is an internal construction from the published
`DomainBaseTransport`, `DomainCoverBaseTransport`, `DomainCovering`,
`DomainAlgebraPresheaf` and `DomainAlgebraSheaf` modules and Mathlib's
site equivalence construction. Its proof transports actual finite
covering witnesses using the already constructed algebra equivalence
and spectrum homeomorphism. It makes no additional assertion from the
original literature and uses no private peer draft.

The hypotheses retain trivial valuations, nilpotents, zero quotient
algebras, empty spectra and permitted empty finite covers. The result
concerns the finite point-covering topology on full represented domains
over one affinoid and its transport along an invertible bounded base
map. Arbitrary noninvertible analytic base change, completed tensor
products, unrestricted analytic atlases, analytic étale and quasi-étale
sites, equivariant sheaves and Harris tower constructions remain
separate obligations.
