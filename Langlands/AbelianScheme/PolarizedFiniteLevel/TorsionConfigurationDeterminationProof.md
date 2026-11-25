# Proof: at large level, torsion configurations determine data over algebraically closed fields

Module `Langlands.AbelianScheme.PolarizedFiniteLevel.TorsionConfigurationDeterminationProof`. The
theorem

```lean
theorem Langlands.AbelianScheme.PolarizedFiniteLevel.torsionConfigurationDetermination :
    TorsionConfigurationDeterminationStatement.{u}
```

proves `TorsionConfigurationDeterminationStatement` (module
`TorsionConfigurationDeterminationStatement`) at an arbitrary universe `u`. Unfolded, the
statement is

```lean
∀ (P : Prerequisites.{u}) (g d : ℕ), 0 < g → 0 < d →
  ∃ N : ℕ, ∀ n : ℕ, N ≤ n →
    ∀ (K : Type u) [Field K] [IsAlgClosed K], (n : K) ≠ 0 →
      ∀ a b : Datum P (Spec (CommRingCat.of K)) g d n,
        a.TorsionConfigurationEquivalent b → Isomorphic a b
```

In words: for the published prerequisites `P` and `0 < g`, `0 < d`, there is a bound `N`
(depending on `P`, `g`, `d` only) such that for every level `n ≥ N`, every algebraically closed
field `K` with `(n : K) ≠ 0` and any two ordinary polarized data `a`, `b` over `Spec K` whose
torsion configurations are equivalent (`Datum.TorsionConfigurationEquivalent`, module
`TorsionConfiguration`), `a` and `b` are isomorphic: some isomorphism of the abelian schemes
carries the polarization and every ordered level section of `a` to those of `b`.

## Proof as implemented

The proof is a single term.

1. `torsionConfigurationDetermination_of_cubicFieldEmbedding` (module
   `TorsionConfigurationDeterminationReduction`) is a proved definition of type
   `CubicFieldEmbeddingStatement.{u} → CubicBundlePolarizationDeterminationStatement.{u} →
   TorsionConfigurationDeterminationStatement.{u}`. Equivalent torsion configurations give
   cubic embeddings of the two abelian varieties whose projective images agree at every labelled
   torsion point; for `n` beyond a bound uniform in the field, the level and the data, the
   torsion points determine the kernel ideal sheaves, so the two embeddings have equal kernels.
   This gives an isomorphism of the abelian schemes that preserves the identity and the ordered
   level sections and pulls the cubic bundle of `b` back to that of `a`; the polarization
   statement, applied with the structure line bundle of the base as twist, then shows that it
   carries the polarization.
2. `cubicFieldEmbedding` (module `CubicFieldEmbeddingProof`) proves
   `CubicFieldEmbeddingStatement.{u}`, Lefschetz's theorem for the canonical cubic bundle over a
   field.
3. `cubicBundlePolarizationDetermination` (module `CubicBundlePolarizationDeterminationProof`)
   proves `CubicBundlePolarizationDeterminationStatement.{u}`: an isomorphism of abelian schemes
   that pulls the cubic bundle of `b` back to that of `a` twisted by a line bundle from the base
   carries the polarization of `b` to that of `a`.

## Declarations

- `torsionConfigurationDetermination : TorsionConfigurationDeterminationStatement.{u}`
  (theorem).

## Provenance

The statement is derived; its page notes that GIT does not state it, but contains its last step
for linearly rigidified data. D. Mumford, J. Fogarty and F. Kirwan, *Geometric Invariant Theory*,
3rd enlarged edition (1994), registered as
`provided-ec58cb66687d0d54d9e39b6ec21281b651fe3a6d039f9b5d099c79791671233f` (PDF page = printed
page + 13), Chapter 7, §2:

- Definition 7.2, printed p. 129 (PDF page 142): the functor `𝒜_{g,d,n}` of polarized abelian
  schemes with level `n` structure; Definition 7.6, printed p. 130 (PDF page 143): the functor
  `ℋ_{g,d,n}` of linearly rigidified ones.
- Printed p. 131 (PDF page 144): "the whole structure defining `α ∈ ℋ_{g,d,n}(S)` is determined
  only by (a) the embedding `I : X ↪ (P_m × S)`, (b) the `2g + 1`-sections of `X/S`:
  `ε, σ_1, σ_2, …, σ_{2g}`"; the identity section determines the group law, the `σ_i` the level
  structure, and `6ω = Λ(L^Δ(ω)³)` determines `ω` because the group of `S`-homomorphisms from
  `X` to `X̂` has no torsion. The theorem here uses this argument without the rigidification:
  the polarization step is `cubicBundlePolarizationDetermination`.
