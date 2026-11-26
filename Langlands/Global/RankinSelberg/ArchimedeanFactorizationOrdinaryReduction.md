# The factorization over S and the infinite places from ordinary archimedean tests

Module `Langlands.Global.RankinSelberg.ArchimedeanFactorizationOrdinaryReduction`, namespace
`Langlands.Global.RankinSelbergGlobal`. The target `ArchimedeanFactorizationStatement` is the
factorization of the partial Rankin–Selberg Whittaker integrals over `S` and the infinite
places, for both ranks (Cogdell 2004, proof of Theorem 4.1, printed pp. 219–220). This module
reduces it to one global comparison, one local functional equation and four assertions of
ordinary nonvanishing at single archimedean places. It proves the reduction; it proves none of
the six premises.

## Two new statements: ordinary nonvanishing in equal rank

`RealEqualOrdinaryPlaceTestsPositiveRankStatement` quantifies over a number field `F` with
`AdeleQuotient F` compact, a unitary additive character `ψ` of the adeles trivial on `F`, a
rank index `r` with `0 < r` (so groups `GL_(r+1)` of rank at least two), two actual cuspidal
realizations `T`, `T'` of `GL_(r+1)`, a real place `v`, the scale `a ∈ ℝˣ` of the component of
`ψ` at `v` (`IsRealAdditiveComponent`), and parameter lists `d`, `d'` of `T` and `T'` at `v`
(`HasRealPlaceParameter`). It asserts that there are

- functions `W`, `W'` on `GL_(r+1)(ℝ)` that are actual restrictions at `v` of global Whittaker
  functions of `T` for `ψ` and of `T'` for `ψ⁻¹` (`IsRealPlaceWhittaker`),
- a Schwartz function `Φ` on `ℝ^(r+1)` and real quotient measure data `D` on
  `N_(r+1)(ℝ) \ GL_(r+1)(ℝ)`,

such that for every real `σ` some `s` with `σ < Re s` has
`realEqualIntegral D W W' Φ s ≠ 0`. Here `realEqualIntegral D W W' Φ s` is the integral
`Ψ(s; W, W', Φ) = ∫ W(g) W'(g) Φ(e_(r+1) g) |det g|^s dg` over the quotient for the measure of
`D` (Jacquet 2009, display (2.6)).

`ComplexEqualOrdinaryPlaceTestsPositiveRankStatement` is the same assertion at a complex place
`w`, with the scale `a ∈ ℂˣ` (`IsComplexAdditiveComponent`), complex parameter lists
(`HasComplexPlaceParameter`), restrictions satisfying `IsComplexPlaceWhittaker`, a Schwartz
function on `ℂ^(r+1)`, complex quotient measure data, and `complexEqualIntegral`, whose
absolute value is the normalized one `|z|²`.

Neither statement involves a dual integral or a contragredient realization. They are the
equal-rank counterparts of the published `RealUnequalOrdinaryPlaceTestsStatement` and
`ComplexUnequalOrdinaryPlaceTestsStatement` (module `UnequalPlaceTestsFromOrdinary`), which
assert, for ranks `t < r`, one actual pair `W`, `W'` and quotient measure data whose ordinary
integral `Ψ(s; W, W')` is nonzero at points arbitrarily far to the right. The rank `GL_1`
(`r = 0`) is excluded because the Library treats it separately: the published reduction
`equalWhittakerPositiveRankReduction` supplies the rank-one tests from the real and complex
Tate theories.

## The reduction

```
def ArchimedeanFactorizationOrdinaryReductionStatement : Prop :=
  InfiniteWhittakerSliceModelStatement.{u, uQ} → RealPlaceFunctionalEquationStatement.{u} →
    RealUnequalOrdinaryPlaceTestsStatement.{u} → ComplexUnequalOrdinaryPlaceTestsStatement.{u} →
    RealEqualOrdinaryPlaceTestsPositiveRankStatement.{u} →
    ComplexEqualOrdinaryPlaceTestsPositiveRankStatement.{u} →
    ArchimedeanFactorizationStatement.{u, uQ}
```

The premises are:

- `InfiniteWhittakerSliceModelStatement` (module `EqualInfiniteWhittakerSliceReduction`): for
  an actual cuspidal tensor presentation, one normalized linear model map at each infinite place
  whose line contains every one-place slice of the global Whittaker functional;
- `RealPlaceFunctionalEquationStatement` (module `ArchimedeanFunctionalEquationStatement`): the
  conjunction of the unequal-rank and equal-rank archimedean functional equations at the real
  places for actual restrictions (Jacquet 2009, Theorem 2.1);
- the four ordinary nonvanishing statements above.

The complex-place functional equations are not premises: the Library proves
`ComplexPlaceFunctionalEquationStatement` as `complexPlaceFunctionalEquation` (module
`ComplexPlaceFunctionalEquationProof`), and the theorem uses its two conjuncts.

## Proof

Two lemmas carry ordinary nonvanishing to the full equal-rank place tests of the published
`RealEqualPlaceTestsPositiveRankStatement` and `ComplexEqualPlaceTestsPositiveRankStatement`
(module `EqualWhittakerPositiveRankReduction`), which ask for one test whose ordinary integral
and whose dual integral `Ψ(s; W̃, W̃', Φ̂)` are both holomorphic on a right half-plane with a
nonzero value there.

- `holomorphicNonzeroOnRightHalfPlane_of_frequently`: a function differentiable on
  `{s | σ < Re s}` that is nonzero at points arbitrarily far to the right satisfies
  `HolomorphicNonzeroOnRightHalfPlane`; take a nonzero value to the right of `σ`.
- `realEqualPlaceTestsPositiveRank_of_ordinary`: given the real equal-rank functional equation
  and the real ordinary statement, take the ordinary witness `W`, `W'`, `Φ`, `D`. The published
  `realPlaceEqualPairConvergence` gives a half-plane on which its ordinary integral is
  differentiable, so the previous lemma applies. The published
  `realEqualDualNonvanishing_of_equation` (module `ArchimedeanDualNonvanishing`) then gives the
  same property for the dual integral of the same test, through the functional equation; it
  uses the contragredient realizations and their parameters supplied by the place-test
  statement.
- `complexEqualPlaceTestsPositiveRank_of_ordinary`: the same argument at a complex place, with
  `complexPlaceEqualPairConvergence` and `complexEqualDualNonvanishing_of_equation`, the latter
  applied to the equal-rank conjunct of `complexPlaceFunctionalEquation`.
- `infiniteWhittakerSliceModelPositiveRank_of_all`: `InfiniteWhittakerSliceModelStatement`
  specializes to its positive-rank form `InfiniteWhittakerSliceModelPositiveRankStatement`.

`archimedeanFactorizationOrdinaryReduction` proves the two conjuncts of the target.

- Unequal ranks. The published `realUnequalPlaceTests_of_ordinary` and
  `complexUnequalPlaceTests_of_ordinary` (module `UnequalPlaceTestsFromOrdinary`) give
  `RealUnequalPlaceTestsStatement` and `ComplexUnequalPlaceTestsStatement` from the unequal-rank
  ordinary statements and the unequal-rank conjuncts of the real and complex functional
  equations. With the slice comparison, `unequalInfiniteWhittakerSliceReduction` gives
  `UnequalPointwiseFactorizationStatement`, and `unequalArchimedeanFactorizationReduction`
  (module `ArchimedeanFactorizationReduction`) integrates it to
  `UnequalArchimedeanFactorizationStatement`, using the proved measure statements
  `UnipotentClass.unipotentClassProductStatement` and `RectangleTate.rectangleTateStatement`.
- Equal ranks. `equalWhittakerPositiveRankReduction` takes the positive-rank slice comparison
  and the two positive-rank place tests obtained by the lemmas above and gives
  `EqualArchimedeanFactorizationStatement`.

The proof uses only the standard axioms `propext`, `Classical.choice` and `Quot.sound`.

## Provenance

Internal. The splitting of Cogdell's argument (J. W. Cogdell, *Analytic theory of
L-functions for GL_n*, 2004, proof of Theorem 4.1, printed pp. 219–220) into a slice comparison
and local tests is that of the published reductions named above. The passage from a nonzero
ordinary integral to a nonzero dual integral of the same test through the local functional
equation follows the structure of H. Jacquet, *Archimedean Rankin–Selberg integrals* (2009),
Theorem 2.1: the dual integral is the ordinary one times a unit epsilon factor and a ratio of
L-factors, up to the central sign. The ordinary nonvanishing assertions correspond to the
existence of tests with nonzero integrals that follows from Jacquet's Theorems 2.3, 2.6 and
2.7 (pp. 8–10); this module does not prove them.
