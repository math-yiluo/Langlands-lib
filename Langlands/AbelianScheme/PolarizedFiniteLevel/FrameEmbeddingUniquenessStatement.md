# Uniqueness of frame-normalized cubic embeddings

`Langlands.AbelianScheme.PolarizedFiniteLevel.FrameEmbeddingUniquenessStatement` is a
proposition definition (universe `u`). It is a statement target only; this module proves
nothing.

## The statement

For `P : Prerequisites.{u}`, a scheme `S`, natural numbers `g d n m`, a datum
`a : Datum P S g d n`, a family `ρ : Fin (m + 2) → Fin (2*g) → ZMod n` and two morphisms
`ψ ψ' : a.abelian.X.left ⟶ RelativeProjectiveSpace S m`: if `a.frameLocus ρ = ⊤` and both
`ψ` and `ψ'` are frame-normalized cubic embeddings of `a` for `ρ`
(`Datum.IsFrameEmbedding`, module `FrameEmbedding`), then `ψ = ψ'`.

## Mathematical content and provenance

This is the uniqueness half of the statement that a projective frame determines the linear
rigidification: Mumford–Fogarty–Kirwan, *Geometric Invariant Theory*, 3rd ed. (1994),
§7.2, registered source
`provided-ec58cb66687d0d54d9e39b6ec21281b651fe3a6d039f9b5d099c79791671233f`
(Definitions 7.5–7.6, printed p.130; the free `PGL(m+1)` action on linear rigidifications,
printed p.135), in the frame-normalized form of `FrameChartRepresentabilityStatement.md`.

Proof sketch. Write `M = π_* L³` (`a.rigidificationModule`), `ev_j : M → P_{ρ j}^* L³` for
the torsion evaluations and `Λ = P_{ρ (m+1)}^* L³` for the last evaluation line. A morphism
`ψ` over `S` is the linear-system morphism of `ψ^* 𝒪(1)` and the pulled-back coordinates
`X_i`. The two `cubic` witnesses are independent line bundles `N` (for `ψ`) and `N'` (for
`ψ'`) on `S`: `ψ^* 𝒪(1) ≅ L³ ⊗ π^* N` and `ψ'^* 𝒪(1) ≅ L³ ⊗ π^* N'`. By adjunction the
coordinates of `ψ` give morphisms `t_i : N^{-1} → M`, and those of `ψ'` give
`t'_i : N'^{-1} → M`. The `basis` condition says `ev_j ∘ t_i = 0` for `i ≠ j ≤ m`, and the
`unit` condition says that `ev_{m+1} ∘ t_i` is one morphism `μ : N^{-1} → Λ` for all `i`;
likewise `ev_{m+1} ∘ t'_i = μ' : N'^{-1} → Λ`. Because the frame locus is `⊤`, the joint
evaluations omitting one index are isomorphisms on the opens of a cover of `S`, hence
isomorphisms. In the splitting `M ≅ ⊕_{j ≤ m} P_{ρ j}^* L³` omitting the last point, the
`i`-th component `c_i` of `ev_{m+1}` is an isomorphism (otherwise the joint evaluation
omitting `ρ i` would not be one). Hence `t_i = τ_i ∘ μ` and `t'_i = τ_i ∘ μ'` with the same
`τ_i : Λ → M` determined by the frame evaluations alone. Both `μ` and `μ'` are isomorphisms,
since the coordinates generate `𝒪(1)` on all of relative projective space, so their common
value at the last point generates. Put `θ = (μ')^{-1} ∘ μ : N^{-1} ≅ N'^{-1}`; then
`t'_i ∘ θ = t_i` for every `i`. Dualizing `θ` and pulling back along `π` gives an
isomorphism `L³ ⊗ π^* N ≅ L³ ⊗ π^* N'`, hence `ψ^* 𝒪(1) ≅ ψ'^* 𝒪(1)`, carrying the
coordinates of `ψ` to those of `ψ'`; by invariance of linear-system morphisms under such an
isomorphism, `ψ = ψ'`.

## Use

The reduction of `FrameChartRepresentabilityStatement`
(`frameChartRepresentability_of_frameHilbertLocus`) uses it to show that the classifying
natural transformation is injective: isomorphic data have the same embedded family.
