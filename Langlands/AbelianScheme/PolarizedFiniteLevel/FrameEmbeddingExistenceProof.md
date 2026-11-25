# Proof: existence of frame-normalized cubic embeddings

Module `Langlands.AbelianScheme.PolarizedFiniteLevel.FrameEmbeddingExistenceProof`. The theorem

```lean
theorem Langlands.AbelianScheme.PolarizedFiniteLevel.frameEmbeddingExistence :
    FrameEmbeddingExistenceStatement.{u}
```

proves `FrameEmbeddingExistenceStatement` (module `FrameEmbeddingExistenceStatement`) at an
arbitrary universe `u`. Unfolded, the statement is

```lean
∀ (P : Prerequisites.{u}) (S : Scheme.{u}) [IsLocallyNoetherian S] (g d n : ℕ), 0 < d →
  ∀ (a : Datum P S g d n) (ρ : Fin (cubicProjectiveDimension g d + 2) → Fin (2 * g) → ZMod n),
    a.frameLocus ρ = ⊤ →
      ∃ ψ : a.abelian.X.left ⟶ RelativeProjectiveSpace S (cubicProjectiveDimension g d),
        a.IsFrameEmbedding ρ ψ
```

In words: for the published prerequisites `P`, a locally noetherian scheme `S`, natural numbers
`g d n` with `0 < d`, a datum `a` over `S` and a family `ρ` of `m + 2` level coefficient tuples,
`m = cubicProjectiveDimension g d`, whose projective frame locus is the whole base, there is a
morphism `ψ` from the abelian scheme of `a` to relative projective `m`-space over `S` that is a
frame-normalized cubic embedding of `a` for `ρ` (`Datum.IsFrameEmbedding`, module
`FrameEmbedding`): a closed immersion over `S` with `ψ^* 𝒪(1)` isomorphic to the cubic bundle
twisted by a line bundle pulled back from `S`, sending the torsion point `ρ j` (`j ≤ m`) to the
`j`-th coordinate point and `ρ (m + 1)` to the point with all coordinates equal.

## Proof as implemented

The proof is a single term.

1. `frameEmbeddingExistence_of_cubicFieldEmbedding` (module `FrameEmbeddingReduction`) is a
   proved definition of type `CubicFieldEmbeddingStatement.{u} →
   FrameEmbeddingExistenceStatement.{u}`. When the frame locus is the whole base, the evaluation
   of the direct image of the cubic bundle at the frame points is an isomorphism; this gives a
   frame of the direct image, whose sections define, by Lefschetz's theorem in its relative form,
   a closed immersion into `ℙ^m_S` normalized at the frame points.
2. `cubicFieldEmbedding` (module `CubicFieldEmbeddingProof`) proves
   `CubicFieldEmbeddingStatement.{u}`, Lefschetz's theorem for the canonical cubic bundle of an
   ordinary polarized datum over a field.

## Declarations

- `frameEmbeddingExistence : FrameEmbeddingExistenceStatement.{u}` (theorem).

## Provenance

D. Mumford, J. Fogarty and F. Kirwan, *Geometric Invariant Theory*, 3rd enlarged edition (1994),
registered as `provided-ec58cb66687d0d54d9e39b6ec21281b651fe3a6d039f9b5d099c79791671233f` (PDF
page = printed page + 13), Chapter 7, §2: Definition 7.5, printed p. 130 (PDF page 143), a
linear rigidification `φ : P(ℰ) ≅ P_m × S` of a polarized abelian scheme, `ℰ = π_*(L^Δ(ω)³)`;
printed p. 131 (PDF page 144), the canonical embedding `X → P(ℰ) ≅ P_m × S` it determines. In
the theorem here the linear rigidification is supplied by the frame of torsion points.
