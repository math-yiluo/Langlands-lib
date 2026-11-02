# Local projective morphisms from actual evaluation

Let `p : X ⟶ S` be a morphism of schemes, `M` a module sheaf on `S`,
`L` a line bundle on `X`, and `ev : M ⟶ p_* L` an actual module-sheaf
morphism. A genuine frame `e` of rank `n + 1` on `U` supplies evaluated
sections over each inverse-image open `p⁻¹(W)`, for `W ≤ U`.

`openSection` converts an actual section on an open subscheme into a global
section of the pullback module to that subscheme. It uses the actual restriction
isomorphism and the canonical comparison from restriction to pullback.
`openSection_smul` proves that scalars are transported by the canonical
`topIso` for the open subscheme. The proof combines semilinearity of restriction,
the scalar formula for the restriction-section isomorphism, and linearity of
the pullback comparison.

`evaluationBase` is the actual morphism `p⁻¹(W) ⟶ W` obtained by restricting
`p`. `evaluationBase_scalar` proves its formula on global functions using the
structure-sheaf formula for the restriction. `evaluationLineBundle` is the
actual pullback of `L` to `p⁻¹(W)`. Applying `openSection` to the evaluated
frame basis defines `localEvaluationSections` in this line bundle.

`localEvaluationSections_change` identifies the sections for a second frame
`f` with the linear change of the sections for `e`. The coefficient map is
exactly `coordinatesOnOpen` applied to the change from `e.dual` to `f.dual`.
The proof applies the published evaluation row law, distributes the additive
section conversion over the finite sum, and uses the scalar formulas and
coefficient base-change identity. In particular the row law is proved for the
actual sections; it is not an additional input.

If the local evaluation sections generate at every point, `localEvaluationMap`
is their actual relative linear-system morphism
`p⁻¹(W) ⟶ RelativeProjectiveSpace W n`. `localEvaluationMap_toBase` proves
that its composite with the projective-space projection is `evaluationBase`.
`localEvaluationSections_change_generate` shows that the same concrete
pointwise generation property holds after changing frames, since the
coefficient matrix is invertible.

`relativeLinearSystemMap_linearChange` is a supporting relative-coordinate
identity. The proof compares the projections to the base and to polynomial
projective space, then uses the published coordinate-change theorem for the
ordinary linear-system map. `scalarsFromBase_comp_toSpecΓ` identifies the
associated global-function scalar map with `p.appTop`.
`localEvaluationMap_change` combines these identities with the proved section
change to show that the local evaluation maps transform by the actual relative
projective action of the dual-frame coordinate change.

This construction is derived from `EvaluationCoordinates`, the existing
linear-system morphism and its coordinate-change identities, and the actual
scheme and module restriction maps. It holds over arbitrary schemes in the
common universe and for an arbitrary module-sheaf evaluation. Pointwise
generation of the displayed sections is an explicit hypothesis of the map
construction. This unit does not prove generation from an abelian scheme,
compatibility across smaller opens, a global glued morphism, an embedding,
or the host moduli representability theorem.
