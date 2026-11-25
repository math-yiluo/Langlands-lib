# Proof: torsion bracket maps with finitely many configurations in each geometric fibre

Module `Langlands.AbelianScheme.PolarizedFiniteLevel.TorsionBracketMapProof`. The theorem

```lean
theorem Langlands.AbelianScheme.PolarizedFiniteLevel.torsionBracketMap :
    TorsionBracketMapStatement
```

proves `TorsionBracketMapStatement` (module `TorsionBracketMapStatement`; the statement has no
universe parameter). Unfolded, the statement is

```lean
∀ (P : Prerequisites.{0}) (g d : ℕ), 0 < g → 0 < d →
  ∃ N : ℕ, ∀ n : ℕ, N ≤ n → ∀ (T : LevelBase n) (b : Datum P T.obj g d n),
    ∃ (m : ℕ)
      (j : T.obj ⟶
        Langlands.AlgebraicGeometry.ProjectiveSpace (Localization.Away (n : ℤ)) m),
      ∀ (K : Type) [Field K] [IsAlgClosed K]
        (y : Spec (CommRingCat.of K) ⟶
          Langlands.AlgebraicGeometry.ProjectiveSpace (Localization.Away (n : ℤ)) m),
        ∃ s : Finset (Spec (CommRingCat.of K) ⟶ T.obj),
          ∀ t : Spec (CommRingCat.of K) ⟶ T.obj, t ≫ j = y →
            ∃ t' ∈ s, (b.pullback t).TorsionConfigurationEquivalent (b.pullback t')
```

In words: for the published prerequisites `P : Prerequisites.{0}` and `0 < g`, `0 < d`, there is
a bound `N` such that for every level `n ≥ N`, every level base `T` (a locally noetherian scheme
on which `n` is a unit) and every datum `b` over `T`, there is a morphism `j` from `T` to a
finite projective space over `Spec ℤ[1/n]` with the following property: for every algebraically
closed field `K` and every `K`-point `y` of the projective space there is a finite set `s` of
`K`-points of `T` such that the pullback of `b` along every `K`-point `t` with `t ≫ j = y` has a
torsion configuration equivalent to that of its pullback along some member of `s`.

## Proof as implemented

The proof is a single term.

1. `torsionBracketMap_of_cubicFieldEmbedding` (module `TorsionBracketMapReduction`) is a proved
   definition of type `CubicFieldEmbeddingStatement.{0} → TorsionBracketMapStatement`. It takes
   the level bound of the frame-locus cover obtained from Lefschetz's theorem
   (`frameLocusCover_of_cubicFieldEmbedding`), chooses a bracket chart around every point of
   `T`, trivializes the `n`-th tensor powers of the torsion evaluation lines, glues the bracket
   coordinates into `j`, and bounds the configuration classes in a fibre by the finitely many
   possible bracket ratios.
2. `cubicFieldEmbedding.{0}` (module `CubicFieldEmbeddingProof`) proves
   `CubicFieldEmbeddingStatement.{0}`, Lefschetz's theorem for the canonical cubic bundle of an
   ordinary polarized datum over a field.

## Declarations

- `torsionBracketMap : TorsionBracketMapStatement` (theorem).

## Provenance

The statement is an internal intermediate statement of the Library; its page cites no
literature source. Its bracket coordinates are the determinants of evaluation at labelled
torsion points described on the page of `LargeLevelQuasiFiniteProjectiveStatement`. The
reduction `torsionBracketMap_of_cubicFieldEmbedding` has Lefschetz's embedding theorem as its only
premise; the source of that theorem is given on the page of `CubicFieldEmbeddingProof`.
