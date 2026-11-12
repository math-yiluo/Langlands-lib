# Ordinary inverse image underlying action-sheaf inverse image

Worker 151, Task 5297. Derived comparison construction supporting Renard
III.3.2, printed p.84 / PDF p.90, the restriction-functor paragraph and its
point-restriction sentence, French edition dated 9 July 2026. Registered source:
`renard-2026-representations-groupes-reductifs-padiques`, SHA256
`7b539996793b7c3620e72e1e389588eb42d1a8e91d6f68b2eead5c2e2ffc182c`.

Renard uses ordinary restriction of the underlying complex sheaf. The existing
`SectionActions.actionInverseImage` implements equivariant inverse image by
left Kan extension and sheafification on the published transport sites. This
unit constructs a natural comparison with Mathlib's ordinary sheaf inverse
image. It is an internal comparison of those existing constructions, rather
than a separately printed assertion or a replacement inverse-image object.

All declarations have prefix
`Langlands.Sheaf.Renard.SectionActions.InverseImageComparison`. The group and
both base spaces are universe-zero types. The assumptions are a group G,
topological spaces X and Y with G-actions whose individual translations are
continuous, and a continuous equivariant map f from X to Y. Joint continuity,
local profiniteness and countability at infinity are unnecessary for this
comparison; the t.d. continuous-action setting in the source is included.
Coefficients are actual complex vector spaces, `ModuleCat ℂ`.

`commaInclusion` sends an ordinary inverse-image comma object to its label-one
transport comma object. `commaInclusion_label_one` proves that a morphism
between two such objects has label one, by its comma triangle.
`commaInclusionFullyFaithful` therefore recovers its original open inclusion.
`preimageOpenIso` gives the original transport isomorphism from the inverse
translate of an open to that open. For an arbitrary comma object with label g
and target open V, `commaInclusion_essSurj` uses this isomorphism to replace V
by its inverse translate under g. Equivariance of f gives the required
ordinary inclusion. Consequently `commaInclusion_isEquivalence` identifies
the two actual comma indexing categories.

`restrictedUnit` is the transport left Kan extension's original unit
restricted to ordinary opens. `restrictedPointwise` restricts its pointwise
colimit cocones along that comma equivalence. Those cocones are definitionally
the ordinary extension cocones, so `restricted_isLeftKanExtension` establishes
the ordinary universal property. `presheafObjectIso` is the canonical
uniqueness isomorphism between this extension and the existing ordinary Kan
extension. `restrictedUnit_presheafObjectIso_hom` records that it preserves the
units. Naturality of the units and the ordinary universal property give
`presheafIso`, natural in every original transport presheaf and morphism.

The published inclusion of ordinary opens into transport opens is both
continuous and cocontinuous. Its Mathlib
`pushforwardContinuousSheafificationCompatibility` therefore identifies
restriction of transport sheafification with ordinary sheafification of the
restriction. `presheafSheafIso` composes the inverse of this compatibility
with `presheafIso`. `siteIso` restricts that natural isomorphism to the actual
sheaf categories. Finally `toSheafIso` uses the published transport-sheaf
category equivalence and Mathlib's `TopCat.Sheaf.pullbackIso`. Its type is the
natural isomorphism

    actionInverseImage f hf ⋙ toSheaf G X (ModuleCat ℂ)
      ≅ toSheaf G Y (ModuleCat ℂ) ⋙
          TopCat.Sheaf.pullback (ModuleCat ℂ) (TopCat.ofHom f).

Thus forgetting equivariance after the actual action-sheaf inverse image is
naturally isomorphic to ordinary inverse image of the original underlying
sheaf. The comparison applies to general continuous equivariant maps and
hence to the subgroup-space inclusions used for restriction in III.3.2,
after the existing subgroup restriction. Smoothness of the entire inverse
image is supplied separately by `SmoothInverseImage`. This unit does not yet
construct the ordinary inverse-image stalk isomorphism or its compatibility
with the original stabilizer representation, the singleton equivalence,
induction or coinvariant sheaves, or any of the main III.3 theorem statements.
