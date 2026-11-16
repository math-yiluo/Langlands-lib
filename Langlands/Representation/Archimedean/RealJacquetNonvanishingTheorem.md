# Proof of `RealJacquetNonvanishingStatement` (nonvanishing of the real Jacquet module)

Module: `Langlands.Representation.Archimedean.RealJacquetNonvanishingTheorem`.

Main theorem:
`Langlands.Archimedean.realJacquetNonvanishing :
Langlands.Archimedean.RealJacquetNonvanishingStatement.{uV}`. The theorem uses only the axioms
`propext`, `Classical.choice` and `Quot.sound`.

## What is proved

`RealJacquetNonvanishingStatement` is in the Library module
`Langlands.Representation.Archimedean.RealJacquetFiniteDimensional`. Let `V` be an irreducible
admissible `(𝔤𝔩_n(ℝ), O(n))`-module (`IsRealGKModule n ρ π`, `IsIrreducibleGKModule ρ π`,
`IsAdmissibleGKModule ρ`). Then `realJacquetSubspace n π ≠ ⊤`, that is, `𝔫V ≠ V` for the
nilpotent radical `𝔫` of the upper triangular Borel subalgebra (Wallach 1979, 4.14 (1), for
irreducible `V`).

## Proof

The proof is a single application of two results:

- `Langlands.Archimedean.RealJacquetNonvanishing.realJacquetNonvanishingSubquotientReduction :
  RealJacquetNonvanishingSubquotientReductionStatement.{uV}`. This is in the Library module
  `Langlands.Representation.Archimedean.RealJacquetNonvanishingProof` (Worker 723). It says that
  `RealPrincipalSeriesSubquotientStatement.{uV}` implies `RealJacquetNonvanishingStatement.{uV}`,
  by Casselman's matrix-coefficient technique (Wallach 1979, 4.13).
- `Langlands.Archimedean.realPrincipalSeriesSubquotient :
  RealPrincipalSeriesSubquotientStatement.{uV}`, Harish-Chandra's subquotient theorem for
  `GL_n(ℝ)`, from the module
  `Langlands.Representation.Archimedean.RealPrincipalSeriesSubquotientProof`. Its Markdown
  explains the proof, which follows Lepowsky / Wallach, *Real Reductive Groups I*, §3.5.

```lean
theorem realJacquetNonvanishing : RealJacquetNonvanishingStatement.{uV} :=
  RealJacquetNonvanishing.realJacquetNonvanishingSubquotientReduction
    realPrincipalSeriesSubquotient
```

Both imported modules are in the Library. `RealPrincipalSeriesSubquotientProof` and its seven
helper modules `RealSubquotient{Eval,Projection,Symbol,Finite,Average,KType,Main}` were published
from the separate accepted candidate `72a4d5db-6944-471b-8977-a3d4ea8f24c0` of the same task.
