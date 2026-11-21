# The Langlands classification (quotient form) for `GL_n(ℝ)`

Module: `Langlands.Representation.Archimedean.RealLanglandsQuotientProof`.

Worker 373 wrote this module for Task 6201 (`285d5eab-679b-4923-b5a6-c24fb384cd06`). It proves
the task's target.

## What is proved

`Langlands.Archimedean.realLanglandsQuotient : RealLanglandsQuotientStatement.{uV}`.

`RealLanglandsQuotientStatement` is stated in the Library module
`Langlands.Representation.Archimedean.RealGenericParameterReduction`. Fix `n : ℕ`, a complex
vector space `V : Type uV`, a representation `ρ` of `Matrix.unitaryGroup (Fin n) ℝ = O(n)` on
`V` and a Lie algebra map `π : ℂ ⊗[ℝ] 𝔤𝔩_n(ℝ) → End_ℂ(V)`. Assume `IsRealGKModule n ρ π`,
`IsIrreducibleGKModule ρ π` and `IsAdmissibleGKModule ρ`. Then there are a list
`ds : List RealBlock` with `realRank ds = n` and `IsRealLanglandsOrdered ds` (the real parts of
the block exponents are non-increasing), and a nonzero linear map

`B : kFiniteFunctions (realStandardModule n ds) (unitaryCompact ℝ n) → V`

with `IsRealStandardIntertwiner n ρ π ds B`. So `B` carries right translation by `k ∈ O(n)`
to `ρ(k)` and the right derivative along a real matrix `X` to `π(1 ⊗ X)`. This is the existence
half of the Langlands classification (Knapp 1994, Theorem 1(a)-(b); Knapp-Vogan 1995,
Theorem 11.198(d)), with the order convention recorded in
[RealGenericParameterReduction.md](RealGenericParameterReduction.md): every irreducible
admissible `(𝔤𝔩_n(ℝ), O(n))`-module is a nonzero quotient of the `O(n)`-finite part of a
standard module in Langlands order.

The theorem keeps every quantifier and the universe `uV` of the statement, and adds no
hypotheses. It uses only the axioms `propext`, `Classical.choice` and `Quot.sound`.

## Proof

The module adds no argument of its own. It applies the Library's reduction to two Library
theorems:

```lean
theorem realLanglandsQuotient : RealLanglandsQuotientStatement.{uV} :=
  realLanglandsQuotientReduction realPrincipalSeriesQuotient realLanglandsFromPrincipalSeries
```

All names are in the namespace `Langlands.Archimedean`.

- `realLanglandsQuotientReduction : RealLanglandsQuotientReductionStatement.{uV}` (module
  `RealLanglandsQuotientReduction`) proves
  `RealPrincipalSeriesQuotientStatement → RealLanglandsFromPrincipalSeriesStatement →
  RealLanglandsQuotientStatement`. Given `(ρ, π)`, the first statement supplies a list `cs` of
  `n` real characters and a nonzero intertwiner from the `O(n)`-finite principal series
  `realStandardModule n (cs.map RealBlock.character)` to `V`. The second statement turns this
  into the list `ds` and the intertwiner `B` required by the target.
- `realPrincipalSeriesQuotient : RealPrincipalSeriesQuotientStatement.{uV}` (module
  `RealPrincipalSeriesQuotientProof`) is Casselman's subrepresentation theorem (Wallach 1979,
  Theorem 4.18) in quotient form for the upper triangular Borel subgroup of `GL_n(ℝ)`. Every
  irreducible admissible `(𝔤𝔩_n(ℝ), O(n))`-module receives a nonzero intertwiner from the
  `O(n)`-finite principal series of some list of `n` real characters, in no particular order.
  See [RealPrincipalSeriesQuotientProof.md](RealPrincipalSeriesQuotientProof.md).
- `realLanglandsFromPrincipalSeries : RealLanglandsFromPrincipalSeriesStatement.{uV}` (module
  `RealLanglandsFromPrincipalSeriesProof`) starts from such a principal-series intertwiner and
  produces a nonzero intertwiner from the standard module of a list of real blocks of total
  rank `n` in Langlands order, into the same module. It repeatedly exchanges or replaces an
  adjacent inverted pair of blocks along explicit filtrations, with a termination measure
  built from the exponent support. See
  [RealLanglandsFromPrincipalSeriesProof.md](RealLanglandsFromPrincipalSeriesProof.md).

Lean elaborates the application with the reduction's universe `uV` equal to the target's, and
both theorems at that same universe.

## Dependencies

The module imports `RealPrincipalSeriesQuotientProof` and `RealLanglandsFromPrincipalSeriesProof`,
both under `Langlands.Representation.Archimedean` and both already in the Library; the first
imports `RealLanglandsQuotientReduction` (through `RealPrincipalSeriesQuotientReduction`), which
imports the target's module `RealGenericParameterReduction`. It changes no Library file.
