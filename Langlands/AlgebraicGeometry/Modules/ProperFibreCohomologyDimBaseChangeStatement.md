# Invariance of fibre cohomology dimensions under base change

Authors: Worker 5705.

The module `Langlands.AlgebraicGeometry.Modules.ProperFibreCohomologyDimBaseChangeStatement`
defines the proposition `ProperFibreCohomologyDimBaseChangeStatement`. It uses the fibre notation
of `ProperFlatFibreCohomologySemicontinuityStatement` (same namespace): for `g : Y ⟶ T` and a
point `t`, `fibreCohomologyDim g t F p` is `dim_{κ(t)} Hᵖ(Y_t, F_t)`, where `Y_t = Y ×_T Spec κ(t)`
and `F_t` is the pullback of `F`. The cohomology is the Library's `relativeCohomology`.

## The statement

Let `g : Y ⟶ T` be proper and `F` an invertible module on `Y` (FLT `Scheme.Modules.IsInvertible`).
Let `h : T' ⟶ T`, `g' : Y' ⟶ T'` and `h' : Y' ⟶ Y` form a cartesian square
(`IsPullback h' g' g h`, i.e. `Y' = Y ×_T T'`), and let `F'` be the pullback of `F` along `h'`.
Then for every point `t'` of `T'` and every `p`:

`dim_{κ(t')} Hᵖ(Y'_{t'}, F'_{t'}) = dim_{κ(h t')} Hᵖ(Y_{h t'}, F_{h t'})`.

The square may be any cartesian square, not only Mathlib's chosen `pullback g h`. There is no
noetherian or flatness hypothesis on `T`, `T'` or `h`. The statement only involves fibres, which
are proper over fields.

## Source and provenance

Derived from D. Mumford, *Abelian Varieties*, Chapter II, §5 (literature id
`mumford-abelian-varieties-chapter-ii-scan`), Corollary 5, printed pp.53–54 (retained PDF
pages 8–9). In the setting of the section's Theorem (p.46), `f : X → Y = Spec A` is a proper
morphism of noetherian schemes and `F` is coherent on `X` and flat over `Y`. Corollary 5 says that
for a flat `A`-algebra `B`, `Hᵖ(X ×_Y Spec B, F ⊗_A B) ≅ Hᵖ(X, F) ⊗_A B`.

The derivation: put `t = h t'`. The fibre `Y'_{t'}` is canonically the base change of the
fibre `Y_t` along the field extension `κ(t) → κ(t')`, and `F'_{t'}` is the base change of `F_t`.
Apply Corollary 5 to the proper morphism `Y_t → Spec κ(t)` of noetherian schemes, to the coherent
sheaf `F_t` (flat over the field `κ(t)`) and to the flat `κ(t)`-algebra `κ(t')`. This gives
`Hᵖ(Y'_{t'}, F'_{t'}) ≅ Hᵖ(Y_t, F_t) ⊗_{κ(t)} κ(t')`, and dimensions are preserved by field
extension. The convention `finrank = 0` for infinite-dimensional spaces does not matter, since
base change preserves infinite dimension too.

The statement is a prerequisite of a proof of the Library's `PicardHilbertPolynomialPiecesStatement`
(Task 6028). It shows that pieces defined by fibre cohomology are compatible with base change.
