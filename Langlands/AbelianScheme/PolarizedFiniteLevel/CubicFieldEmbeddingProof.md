# Proof: the cubic Lefschetz embedding of an ordinary polarized datum over a field

Module `Langlands.AbelianScheme.PolarizedFiniteLevel.CubicFieldEmbeddingProof`. The theorem

```lean
theorem Langlands.AbelianScheme.PolarizedFiniteLevel.cubicFieldEmbedding :
    CubicFieldEmbeddingStatement.{u}
```

proves `CubicFieldEmbeddingStatement` (module `CubicFieldEmbeddingStatement`) at an arbitrary
universe `u`. Unfolded, the statement is

```lean
∀ (P : Prerequisites.{u}) (K : Type u) [Field K] (g d n : ℕ), 0 < d →
  ∀ a : Datum P (Spec (CommRingCat.of K)) g d n,
    Epi a.cubicEvaluationAdjoint ∧
      ∀ (m : ℕ) (b : Module.Basis (Fin (m + 1)) K
          ((relativeGlobalSections a.abelian.X.hom).obj a.cubicBundle.obj))
        (hb : ∀ x : a.abelian.X.left, ∃ i,
          x ∈ nonvanishingLocus a.cubicBundle.obj (b i)),
        IsClosedImmersion (relativeLinearSystemMap a.abelian.X.hom hb)
```

In words: for the published prerequisites `P`, a field `K`, natural numbers `g d n` with `0 < d`
and an actual ordinary polarized datum `a` over `Spec K`, with abelian variety
`π : A → Spec K` and canonical cubic bundle `L³ = a.cubicBundle`:

1. the adjunction counit `π^* π_* L³ → L³` is an epimorphism, so the complete linear system of
   `L³` has no base points;
2. for every `K`-basis `b 0, …, b m` of the global sections of `L³` (with the proof `hb` that the
   sections have no common zero), the morphism `A → ℙ^m_K` they define is a closed immersion.

## Proof as implemented

The proof is a single term that combines two Library theorems.

1. `cubicFieldEmbedding_of_cubeSeparation` (module `CubicFieldEmbeddingReduction`) proves
   `AlgClosedFieldAmpleCubeSeparationStatement.{u} → CubicFieldEmbeddingStatement.{u}`. It
   base-changes the datum to an algebraic closure of `K`, uses flat base change for the global
   sections, and descends the epimorphy of the counit and the closed immersion along the
   faithfully flat morphism `Spec K̄ → Spec K`.
2. `Langlands.AbelianScheme.algClosedFieldAmpleCubeSeparation` (module
   `Langlands.AbelianScheme.AlgClosedFieldAmpleCubeSeparationProof`) proves
   `AlgClosedFieldAmpleCubeSeparationStatement.{u}`: on an abelian scheme over an algebraically
   closed field, the complete linear system of the tensor cube of an ample line bundle has no
   rational base point, separates rational points and separates nonzero rational tangent
   vectors.

Applying the reduction to the separation theorem gives the statement.

## Declarations

- `cubicFieldEmbedding : CubicFieldEmbeddingStatement.{u}` (theorem).

## Provenance

- D. Mumford, *Abelian Varieties* (1970), registered as `mumford-abelian-varieties-full-scan`:
  §17 "Very ample line bundles", Theorem: for an ample line bundle `L` on an abelian variety, `Lⁿ`
  is very ample for `n ≥ 3`; the proof for `L³` reduces to the separation of points and of
  tangent vectors by `|3D|` (page reference to be added). Mumford works over an algebraically
  closed field; the reduction above passes to an arbitrary field.
- D. Mumford, J. Fogarty and F. Kirwan, *Geometric Invariant Theory*, 3rd enlarged edition
  (1994), registered as
  `provided-ec58cb66687d0d54d9e39b6ec21281b651fe3a6d039f9b5d099c79791671233f` (PDF page = printed
  page + 13): Chapter 7, §2, Definition 7.5, printed p. 130 (PDF page 143), the bundle
  `L^Δ(ω)³`, whose direct image is locally free of rank `6^g · d`, and `m = 6^g · d − 1`; printed p. 131 (PDF page
  144), the canonical embedding `X → P(ℰ) ≅ P_m × S` by the sections of `L^Δ(ω)³`, which is the
  embedding of the theorem here over a field.
