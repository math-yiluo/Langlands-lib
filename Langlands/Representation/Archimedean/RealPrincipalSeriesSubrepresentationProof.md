# Casselman's subrepresentation theorem for `GL_n(ℝ)`

Module: `Langlands.Representation.Archimedean.RealPrincipalSeriesSubrepresentationProof`.

## What is proved

- `Langlands.Archimedean.realPrincipalSeriesSubrepresentation :
  RealPrincipalSeriesSubrepresentationStatement.{uV}`. This is the unconditional theorem.
- `Langlands.Archimedean.RealPrincipalSeriesSubrepresentation.of_nonvanishing :
  RealJacquetNonvanishingStatement.{uV} → RealPrincipalSeriesSubrepresentationStatement.{uV}`.
  This is the conditional step used to prove it.

`RealPrincipalSeriesSubrepresentationStatement` (module `RealPrincipalSeriesQuotientReduction`)
is Casselman's subrepresentation theorem (Wallach 1979, Theorem 4.18) for `GL_n(ℝ)` and the
upper triangular Borel subgroup. Every irreducible admissible `(𝔤𝔩_n(ℝ), O(n))`-module `V` has a
nonzero standard embedding `B : V → kFiniteFunctions (realStandardModule n (cs.map
RealBlock.character))` into an `O(n)`-finite principal series, for some list `cs` of `n` real
characters. The theorem is stated for every `n` and every universe `uV` of `V`, with no
assumptions beyond the three in the statement: `V` is a `(𝔤, K)`-module, it is irreducible, and
it is admissible.

`RealJacquetNonvanishingStatement` (module `RealJacquetFiniteDimensional`) says that `𝔫V ≠ V`
for every such `V`, where `𝔫` is the strictly upper triangular subalgebra.

## Proof

The proof only composes results that are already in the Library. It has no new argument of its
own.

`of_nonvanishing` combines four of them:

1. `RealJacquetFiniteGeneration.realJacquetFiniteGeneration` proves
   `RealJacquetFiniteGenerationStatement`, which says `V = U(𝔫) F` for a finite-dimensional
   subspace `F`.
2. `realJacquetFiniteDimensional_of_finiteGeneration` turns this into
   `RealJacquetFiniteDimensionalStatement`, which says `V/𝔫V` is finite-dimensional.
3. `realJacquetModuleFinite_of_finiteDimensional_of_nonvanishing` combines this with the
   hypothesis `RealJacquetNonvanishingStatement` into `RealJacquetModuleFiniteStatement`, which
   says `V/𝔫V` is finite-dimensional and nonzero.
4. `realPrincipalSeriesSubrepresentationJacquetReduction` (module `RealJacquetReduction`)
   derives the subrepresentation theorem from two inputs. One is `RealJacquetModuleFiniteStatement`.
   The other is the Frobenius embedding `RealJacquetFrobeniusStatement`, proved by
   `RealJacquetFrobenius.realJacquetFrobenius`. The reduction takes a common eigenvector of the
   commuting diagonal and sign-reflection operators on the dual of `V/𝔫V`. That eigenvector is
   a nonzero Jacquet functional, and the reduction passes it to the Frobenius embedding.

`realPrincipalSeriesSubrepresentation` applies `of_nonvanishing` to a proof of
`RealJacquetNonvanishingStatement` built from two more Library results:

5. `RealJacquetNonvanishing.realJacquetNonvanishingSubquotientReduction` (module
   `RealJacquetNonvanishingProof`) proves `RealJacquetNonvanishingSubquotientReductionStatement`.
   That statement says Harish-Chandra's subquotient theorem
   `RealPrincipalSeriesSubquotientStatement` implies `RealJacquetNonvanishingStatement`. The
   argument is Casselman's matrix-coefficient technique (Wallach 1979, 4.13), with a Gronwall
   estimate in place of the full asymptotic expansions.
6. `realPrincipalSeriesSubquotient` (module `RealPrincipalSeriesSubquotientProof`) proves
   `RealPrincipalSeriesSubquotientStatement` by Lepowsky's argument (Wallach, *Real reductive
   groups I*, §3.5).

So the proof term is

```lean
theorem realPrincipalSeriesSubrepresentation :
    RealPrincipalSeriesSubrepresentationStatement.{uV} :=
  RealPrincipalSeriesSubrepresentation.of_nonvanishing
    (RealJacquetNonvanishing.realJacquetNonvanishingSubquotientReduction
      realPrincipalSeriesSubquotient)
```

The theorem uses only the axioms `propext`, `Classical.choice` and `Quot.sound`.
