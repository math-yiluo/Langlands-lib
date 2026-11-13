# Smoothness and geometric connectedness of dynamic subgroups over a ring

Worker 220.

This module proves
`Langlands.GroupScheme.dynamicRingSmoothConnected.{u} :
Langlands.GroupScheme.DynamicRingSmoothConnectedStatement.{u}`.
The theorem has precisely the published proposition as its type, with no added
hypothesis. Its ring, group schemes, cocharacter and representing homomorphism
have the quantifiers of the unchanged statement module
`Langlands.GroupScheme.Dynamic.RingSmoothConnectedStatement`.

## Implemented proof

The three smoothness conclusions follow from the published theorem
`Langlands.GroupScheme.dynamicSmooth_ring` in
`Langlands.GroupScheme.Dynamic.SmoothOverRing`.

For geometric connectedness, Mathlib's
`AlgebraicGeometry.geometrically_iff_of_isClosedUnderIsomorphisms` reduces each
goal to connectedness of the pullback along an arbitrary field point
`y : Spec K ⟶ Spec R`. Form the base changes `Gk`, `Hk`, `jk`, and the cocharacter
`Dynamic.baseChangeCocharacter y χ`. Smoothness and affineness of the structural
morphism of `Gk` follow from stability under base change. The pullback scheme
`H ×[Spec R] Spec K` is definitionally the underlying scheme of `Hk`.

The representing property of `j` is preserved by
`SubgroupFunctor.IsRepresentedBy.baseChange`. The three dynamic base-change
identities identify the transported subgroup functor with the dynamic subgroup
of the transported cocharacter. The field theorem
`Langlands.GroupScheme.dynamicConnected` then supplies connectedness of `Hk`.
For the unipotent case no ambient connectedness is required. For the parabolic
and centralizer cases, geometric connectedness of `G.X.hom` supplies
connectedness of `Gk` by `AlgebraicGeometry.pullback_of_geometrically`.

## Published inputs

All group-scheme names in this list are prefixed by `Langlands.GroupScheme`.
These are the published theorems directly applied by the proof:

- `dynamicSmooth_ring`, in `Langlands.GroupScheme.Dynamic.SmoothOverRing`.
- `dynamicConnected`, in `Langlands.GroupScheme.Dynamic.ConnectedProof`.
- `SubgroupFunctor.IsRepresentedBy.baseChange`, in
  `Langlands.GroupScheme.SubgroupBaseChange`.
- `Dynamic.unipotent_baseChange`, `Dynamic.parabolic_baseChange`, and
  `Dynamic.centralizer_baseChange`, in
  `Langlands.GroupScheme.Dynamic.BaseChange`, imported by
  `Langlands.GroupScheme.SubgroupBaseChange`.
- `AlgebraicGeometry.geometrically_iff_of_isClosedUnderIsomorphisms` and
  `AlgebraicGeometry.pullback_of_geometrically`, in
  `Mathlib.AlgebraicGeometry.Geometrically.Basic`.

The proof also uses the defining field
`AlgebraicGeometry.GeometricallyConnected.geometrically_connectedSpace`, in
`Mathlib.AlgebraicGeometry.Geometrically.Connected`, and the Mathlib pullback
instances for `Smooth` and `IsAffineHom` from
`Mathlib.AlgebraicGeometry.Morphisms.Smooth` and
`Mathlib.AlgebraicGeometry.Morphisms.Affine`. These use
`CategoryTheory.MorphismProperty.pullback_snd` from
`Mathlib.CategoryTheory.MorphismProperty.Limits`, with the stability instances
`AlgebraicGeometry.smooth_isStableUnderBaseChange` and
`AlgebraicGeometry.isAffineHom_isStableUnderBaseChange` in the respective
smooth and affine morphism modules.

## Provenance and scope

This is a derived proof from published Library theorems. The ring-level
smoothness theorem and the field connectedness theorem are combined using
arbitrary field base change. The task context credits Worker 3483 with this
route; its referenced draft revision 26 is absent from the carried files, so
this implementation was reconstructed from the current published inputs.

The unchanged statement's paired Markdown gives the source comparison with
Conrad, *Reductive group schemes* (2014), Theorem 4.1.7(2) and the smoothness
assertion of 4.1.7(4). This proof makes no additional source claims and does not
assert existence of representatives. The base ring need not be noetherian,
local or a domain. The parabolic and centralizer connectedness conclusions
retain the geometric connectedness hypothesis on the ambient group.

## Verification

The Lean service compiled the module with no errors or warnings in environment
`5c94c648-e8dc-4002-a50a-071ebf3f6096`. Declaration inspection reports one
universe parameter `u` and only `propext`, `Classical.choice` and `Quot.sound`.
This development check is separate from independent acceptance and publication.
