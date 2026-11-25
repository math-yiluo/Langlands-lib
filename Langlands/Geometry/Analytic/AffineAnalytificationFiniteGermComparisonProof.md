# Proof: flatness and unramifiedness at a point where the analytification is finite

Lean module: `Langlands.Geometry.Analytic.AffineAnalytificationFiniteGermComparisonProof`.

## Result

`Langlands.Analytic.AffineAnalytification.affineAnalytificationFiniteGermComparison`
proves the published statement
`Langlands.Analytic.AffineAnalytification.AffineAnalytificationFiniteGermComparisonStatement.{u, v, w}`
in all universes, with no added hypothesis. The statement, its hypotheses and its source are
documented in `AffineAnalytificationFiniteGermComparisonStatement.md`. In short: for `g :=
saturatedHom K P Q f`, a chart point `y := chart K Q m s` with `g.IsFiniteAt y`, and the prime
`q` of `B` under `y`, it asserts `g.IsUnramifiedAt y ↔ Algebra.IsUnramifiedAt A q` and
`g.IsFlatAt y ↔ (Localization.localRingHom (q.comap f) q f rfl).Flat`.

The module also contains the intermediate theorem

`finiteGermComparison_of_flatness (hchart : AffineAnalytificationChartFlatStatement.{u, v})
(hdom : Domain.FlatnessStatement.{u}) : AffineAnalytificationFiniteGermComparisonStatement.{u, v, w}`,

which shows that only these two flatness inputs come from outside the local argument.

## Proof

Both theorems are one-line compositions.

* `FinitePieceLocal.affineAnalytificationFinitePieceLocal hchart hdom` (module
  `FinitePieceLocalProof`) proves the local statement
  `AffineAnalytificationFinitePieceLocalStatement`. Its Markdown and those of its helper modules
  `FiniteAlgebraNormedModel`, `FinitePieceLocalAlgebra`, `FinitePieceChartMaps`,
  `FinitePieceLocalMaps` and `FinitePieceEngine` describe the argument.
* `finiteGermComparison_of_finitePieceLocal` (module `AffineAnalytificationFiniteGermAssembly`)
  derives the target from the local statement by commutative algebra.
* `finiteGermComparison_of_flatness` composes these two.
* `affineAnalytificationFiniteGermComparison` instantiates `hchart` with
  `affineAnalytificationChartFlat` (module `AffineAnalytificationChartFlatProof`) and `hdom` with
  `PresentedAffinoidAlgebra.Domain.flatness` (module
  `GeneralizedAffinoid.DomainFlatnessProof`).

The axioms used are `propext`, `Classical.choice` and `Quot.sound`.

## Provenance

The target is the pointwise form, for finite points, of Berkovich 1993, Propositions 3.2.10 and
3.3.11, as explained in the target statement's Markdown. The route here differs from Berkovich's.
It does not use Zariski's Main Theorem or sheaves of differentials. It goes through the derived
local statement for finite pieces, whose Markdown explains its provenance and why its condition 4
holds.
