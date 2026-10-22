# Canonical pullback of the structure sheaf

For schemes `X` and `Y` in universe `u` and a morphism `f : X ⟶ Y`,
`Langlands.Scheme.Modules.unitToPushforwardUnit f` is the structure-sheaf
map regarded as a morphism of module sheaves from `O_Y` to `f_* O_X`.
Here `O_X` means exactly `SheafOfModules.unit X.ringCatSheaf`.

`Langlands.Scheme.Modules.pullbackUnitIso f` is the canonical isomorphism
`f^* O_Y ≅ O_X`, using the existing `AlgebraicGeometry.Scheme.Modules.pullback f`.
Its forward map is the adjoint of the preceding structure-sheaf map.
The inverse orientation is available as `(pullbackUnitIso f).symm`.
All categories are the actual scheme-module categories from Mathlib.

This is internal categorical infrastructure specialized from pinned Mathlib
(commit `5ed2965256430c3649e86755f9576b54eca72435`), rather than a new translation
of a literature definition. In
`Mathlib/Algebra/Category/ModuleCat/Sheaf/PullbackFree.lean`,
`SheafOfModules.unitToPushforwardObjUnit` supplies the first map and
`SheafOfModules.pullbackObjUnitToUnit` supplies its adjoint. Mathlib proves the
latter is invertible for a final functor between sites. Inverse image of opens
`TopologicalSpace.Opens.map f.base` is final; the construction uses the existing
instance and the existing pullback-pushforward adjunction. No invertibility or
coherence hypothesis is imposed on the scheme morphism.

The local transparency option permits elaboration across Mathlib's scheme-module
wrappers; it does not add a mathematical assumption. This unit contains two
definitions only. It does not claim a tensor construction, a monoidal structure,
or the identity/composition coherence laws; those laws are separate proof
obligations.
