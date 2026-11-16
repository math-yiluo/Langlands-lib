# Casselman's theorem in quotient form for `GL_n(ℝ)`

Module: `Langlands.Representation.Archimedean.RealPrincipalSeriesQuotientProof`.

Worker 378 wrote this module for Task 6746 (`262dea19-8ca2-4a4d-87d7-f1002ea208d0`), with
Worker 5459. It proves the task's target.

## What is proved

`Langlands.Archimedean.realPrincipalSeriesQuotient : RealPrincipalSeriesQuotientStatement.{uV}`.

`RealPrincipalSeriesQuotientStatement` is stated in the Library module
`Langlands.Representation.Archimedean.RealLanglandsQuotientReduction`. Fix `n : ℕ`, a complex
vector space `V : Type uV`, a representation `ρ` of `Matrix.unitaryGroup (Fin n) ℝ = O(n)` on
`V` and a Lie algebra map `π : ℂ ⊗[ℝ] 𝔤𝔩_n(ℝ) → End_ℂ(V)`. Assume `IsRealGKModule n ρ π`,
`IsIrreducibleGKModule ρ π` and `IsAdmissibleGKModule ρ`. Then there are a list
`cs : List RealCharacterData` with `cs.length = n` and a nonzero linear map

`B : kFiniteFunctions (realStandardModule n (cs.map RealBlock.character)) (unitaryCompact ℝ n) → V`

with `IsRealStandardIntertwiner n ρ π (cs.map RealBlock.character) B`. So `B` carries right
translation by `k ∈ O(n)` to `ρ(k)` and the right derivative along a real matrix `X` to
`π(1 ⊗ X)`. No order condition is imposed on `cs`. Equivalently, every irreducible admissible
`(𝔤𝔩_n(ℝ), O(n))`-module is a nonzero quotient of the `O(n)`-finite part of a principal
series. This is Casselman's subrepresentation theorem (Wallach 1979, Theorem 4.18) in quotient
form, for the upper triangular Borel subgroup of `GL_n(ℝ)`.

The theorem keeps every quantifier and the universe `uV` of the statement, and adds no
hypotheses. It uses only the axioms `propext`, `Classical.choice` and `Quot.sound`.

## Proof

The module adds no argument of its own. It applies the Library's reduction to three Library
theorems:

```lean
theorem realPrincipalSeriesQuotient : RealPrincipalSeriesQuotientStatement.{uV} :=
  realPrincipalSeriesQuotientReduction
    realPrincipalSeriesSubrepresentation
    RealContragredient.realContragredientStatement
    RealPrincipalSeriesDuality.realPrincipalSeriesDuality
```

All names are in the namespace `Langlands.Archimedean`.

- `realPrincipalSeriesQuotientReduction : RealPrincipalSeriesQuotientReductionStatement.{uV}`
  (module `RealPrincipalSeriesQuotientReduction`) proves
  `RealPrincipalSeriesSubrepresentationStatement → RealContragredientStatement →
  RealPrincipalSeriesDualityStatement → RealPrincipalSeriesQuotientStatement`. Its proof
  dualizes `V` to its `O(n)`-finite contragredient `W`, embeds `W` into a principal series
  `PS(cs')`, and transposes the embedding along the two invariant pairings. The result is a
  nonzero intertwiner from `PS(cs)` onto `V`, where `cs` is the list of inverse characters. The
  closure of the `O(n)`-finite principal series under right translation by `O(n)` and under
  right derivatives enters here. It comes from the Library's
  `rightTranslation_mem_kFiniteFunctions_realStandardModule` and
  `rightDerivative_mem_kFiniteFunctions_realStandardModule` (module `RealStandardModuleGKModule`).
- `realPrincipalSeriesSubrepresentation : RealPrincipalSeriesSubrepresentationStatement.{uV}`
  (module `RealPrincipalSeriesSubrepresentationProof`) is Casselman's subrepresentation theorem
  for `GL_n(ℝ)`. Every irreducible admissible `(𝔤𝔩_n(ℝ), O(n))`-module has a nonzero
  `(𝔤, K)`-embedding into the `O(n)`-finite functions of the principal series of some `n` real
  characters. It is proved through the Jacquet module: `V/𝔫V` is finite-dimensional and
  nonzero, and Frobenius reciprocity turns a joint eigenvector of its dual into the embedding.
  The nonvanishing comes from Harish-Chandra's subquotient theorem by Casselman's
  matrix-coefficient argument.
- `RealContragredient.realContragredientStatement : RealContragredientStatement.{uV}` (module
  `RealContragredientProof`) gives, for every irreducible admissible `V`, an irreducible
  admissible `(𝔤, K)`-module `W`, its `O(n)`-finite contragredient. It comes with an invariant
  pairing `W × V → ℂ` that separates the points of `V` and represents every `O(n)`-finite
  linear functional on `W`.
- `RealPrincipalSeriesDuality.realPrincipalSeriesDuality : RealPrincipalSeriesDualityStatement`
  (module `RealPrincipalSeriesDualityProof`) gives the pairing `Q(f, h) = ∫_{O(n)} f(k) h(k) dk`
  between the `O(n)`-finite principal series of pointwise inverse characters. The pairing is
  invariant under `O(n)` and the Lie algebra, and nondegenerate in its second argument.

Lean elaborates the application with the reduction's universe `uV` equal to the target's, and
the subrepresentation and contragredient theorems at that same universe. The duality statement
has no universe parameter.

## Dependencies

The module imports `RealPrincipalSeriesQuotientReduction`,
`RealPrincipalSeriesSubrepresentationProof`, `RealContragredientProof` and
`RealPrincipalSeriesDualityProof`, all under `Langlands.Representation.Archimedean` and all
already in the Library. It changes no Library file.
