# Existence of frame-normalized cubic embeddings

`Langlands.AbelianScheme.PolarizedFiniteLevel.FrameEmbeddingExistenceStatement` is a
proposition definition (universe `u`). It is a statement target only; this module proves
nothing.

## The statement

For `P : Prerequisites.{u}`, a locally noetherian scheme `S`, natural numbers `g d n` with
`0 < d`, a datum `a : Datum P S g d n` and a family
`ρ : Fin (m + 2) → Fin (2*g) → ZMod n` with `m = cubicProjectiveDimension g d`: if
`a.frameLocus ρ = ⊤`, then there is a morphism
`ψ : a.abelian.X.left ⟶ RelativeProjectiveSpace S m` that is a frame-normalized cubic
embedding of `a` for `ρ` (`Datum.IsFrameEmbedding`, module `FrameEmbedding`).

## Mathematical content and provenance

Mumford–Fogarty–Kirwan, *Geometric Invariant Theory*, 3rd ed. (1994), §7.2, registered
source `provided-ec58cb66687d0d54d9e39b6ec21281b651fe3a6d039f9b5d099c79791671233f`: the
embedding of a polarized abelian scheme determined by a linear rigidification
(printed p.131, PDF p.144), with the linear rigidification supplied by the frame.

Proof sketch. Write `M = π_* L³` and `Λ = P_{ρ(m+1)}^* L³`. When the frame locus is `⊤`,
the joint evaluation `M → ⊕_{j ≤ m} P_{ρ j}^* L³` is an isomorphism, and the evaluation at
`ρ (m+1)` has isomorphisms `c_j : P_{ρ j}^* L³ → Λ` as components; so
`τ_j := (evaluation)^{-1} ∘ (inclusion of the j-th summand) ∘ c_j^{-1} : Λ → M` is a frame
`M ≅ Λ^{m+1}`. The adjoints of the `τ_j` are sections of `L³ ⊗ π^* Λ^{-1}`. By Lefschetz's
theorem (`CubicFieldEmbeddingStatement`, with its relative form
`Datum.cubicProjectiveEmbedding_of_fieldEmbedding` in module `CubicEmbeddingReduction`) they
generate, and the resulting linear-system morphism `ψ` to `ℙ^m_S` is a closed immersion
with `ψ^* 𝒪(1) ≅ L³ ⊗ π^* Λ^{-1}`. By construction the torsion point `ρ j` goes to the
`j`-th coordinate point and `ρ (m+1)` to `[1 : … : 1]`.

The local noetherianity of `S` and `0 < d` are the hypotheses under which the Library's
cubic direct-image theorem (`cubicDirectImage`) and the relative Lefschetz reduction apply.

## Use

The reduction of `FrameChartRepresentabilityStatement`
(`frameChartRepresentability_of_frameHilbertLocus`) uses it to classify every datum with
frame locus `⊤` by a morphism to the Hilbert scheme with sections.
