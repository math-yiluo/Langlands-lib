# Two-axis rigidified bundles with isomorphic carriers

Worker 198 wrote this internal module for Task 5678. It works in namespace
`Langlands.AlgebraicGeometry.Picard.TwoAxisRigidifiedLineBundle`, in every
universe, for an arbitrary Library abelian scheme `A` over an arbitrary scheme
`S`.

`mumfordSection_fst` records that the first unit axis `(id, e)` of the
self-product, `mumfordSection A`, is a section of the first pullback
projection.

`nonempty_iso_of_carrierIso` concerns two objects `L` and `M` of the published
category
`TwoAxisRigidifiedLineBundle (unitSection A) (unitSection A) (mumfordSection A)
(twoAxisSecond A) (twoAxis_unit_comp A)`.
These are actual line bundles on `A ×_S A` with compatible trivializations along
both unit axes. This is exactly the category whose isomorphism classes form the
published `classPresheaf` at each test scheme. If the underlying module sheaves
of `L` and `M` are isomorphic, the theorem gives an isomorphism `L ≅ M` that
respects both rigidifications.

Proof.

1. Regard the first trivializations as one-section rigidifications along
   `mumfordSection A`, which has the retraction `pullback.fst`. The published
   `RigidifiedLineBundle.isoOfCarrierIso` (one-section adjustment), with the
   published unconditional `pullbackTensorComparisonIsIso`, corrects the given
   carrier isomorphism to an isomorphism `g₁` respecting the first axis.
2. The second-axis discrepancy of `g₁` is an automorphism of the structure sheaf
   of `A`. By `secondDiscrepancy_restrict_refl` it is trivial after pullback
   along the unit section.
3. The structure morphism of `A` is smooth, proper and geometrically connected.
   The published theorem `smoothProperConnectedGlobalFunctions` therefore makes
   it an isomorphism on global functions. `structureAut_eq_refl_of_section` then
   shows the discrepancy is the identity, so `g₁` also respects the second axis.

The published two-axis `isoMk` packages `g₁`.

The provenance is internal: composition of the Library results named above. The
statement shows that, for abelian schemes, classes of compatible two-axis
rigidified bundles correspond to bundles admitting such rigidifications. Compare
Raynaud's `Pic_(e,f)` in LNM 119, Definition III 2.2(2); no literature statement
is formalized here.
