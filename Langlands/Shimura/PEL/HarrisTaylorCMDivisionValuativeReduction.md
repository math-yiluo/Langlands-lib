# Division-case valuative existence from potential good reduction and the Néron–Ogg–Shafarevich criterion

All declarations are in `Langlands.Shimura.PEL.HarrisTaylorCMWeilLevel`. The
statement `DivisionCMDiscreteValuativeReductionStatement` and the theorems
`cmLevelDvrGoodModel_of_division` and `divisionCMDiscreteValuativeReduction` carry the
variables and all named prerequisites of `DivisionCMDiscreteValuativeExistenceStatement`
(written "…" below). The private lemma `isUnit_natCast_of_connTest` carries only the
setup of `connectedSpecTest`: the unitary data `D`, the charts `C` and the nine
prerequisites `preservation`, `composition`, `unitCoherence`, `associativity`,
`comparison`, `symmetry`, `stability`, `square` and `universality` (written
`connectedSpecTest … R β` below).

## Statement

`DivisionCMDiscreteValuativeReductionStatement …` is the implication

`PotentialSemistableReductionStatement.{0} → AbelianReductionStatement.{0} →
NeronOggShafarevichStatement.{0} → DivisionCMDiscreteValuativeExistenceStatement …`.

The three premises are the published statements of potential semistable reduction
(module `Langlands.AbelianScheme.PotentialSemistableReductionStatement`), of the
abelian reduction criterion for a Néron model (module
`Langlands.AbelianScheme.AbelianReductionStatement`) and of the criterion of Néron,
Ogg and Shafarevich (module `Langlands.AbelianScheme.NeronOggShafarevichStatement`),
all in universe zero. The module proves the implication; it does not prove any of
the three premises.

## Proofs

`isUnit_natCast_of_connTest` (private) reads off from the `torsionUnits` field of the
published admissibility of `connectedSpecTest … R β`, transported to `R` by
`Scheme.ΓSpecIso`, that every positive integer is a unit of `R`.

`cmLevelDvrGoodModel_of_division hsemi habelian hnos hD U` proves
`CMLevelDvrGoodModelStatement … U` (module `HarrisTaylorCMDvrGoodModelReduction`) for
every small level `U` when `D.IsDivision` holds. Let `V`, `K`, `β`, a geometric point
`a` of `Spec K` and a representative `x` at level `U` be given, and let `B` be the
abelian scheme of `x`.

1. Smallness of `U` gives a finite place `v` of `ℚ` with `LevelSmallAt U v`; let `ℓ`
   be its prime. It is a unit of `V` by `isUnit_natCast_of_connTest`. The normalized conditions on `x` give, through
   `determinantDimensionCondition_iff`, the relative dimension `[E : ℚ] n²` of `B`.
2. The criterion `hnos` is applied to `B` and `ℓ`. Its hypothesis is checked at an
   arbitrary strictly Henselian discrete valuation ring `W` over `V` with fraction
   field `L` over `K`, a geometric point `s` of `Spec L` and an element `g` of the
   fundamental group. The unramifiedness and compatibility conditions on `W` and
   `L` are not needed for this.
   - The base change `B_L` of `B` to `L` keeps the rational `A`-action and the
     relative dimension, so the published `divisionPotentialGoodReduction`, which
     uses `hsemi`, `habelian` and `D.IsDivision`, gives potential good reduction of
     `B_L` over `W`.
   - The residue field of `W` has characteristic zero, since every positive integer
     is a unit of `V` and hence of `W`. The published
     `HasPotentialGoodReduction.strictLocalMonodromyExponent` then gives a positive
     integer `m` with `ρ(g)^m = 1` for the full rational Tate monodromy `ρ` of `B_L`
     at `s`.
   - The level orbit of `x` is moved from `a` to the image `s ≫ (Spec L → Spec K)` of
     `s` along a path of fibre functors (`geometricPathExists`,
     `PolarizedWeilLevel.pointMapData`), which keeps the same polarized action. The
     existing `levelDataBaseChange` pulls it back to a positive polarized action on
     `B_L` with a fixed level orbit at `s` and level `U`; the pulled-back dual data
     are constructed from `relativeDualSchemeExistence` and
     `relativeDualSchemeGeometry`.
   - The element `g` itself need not have finite order in the fundamental group;
     what is finite is the order of its image `ρ(g)` under the full rational Tate
     monodromy of `B_L` at `s`, since `ρ(g)^m = 1`. The published
     `primeTateMonodromyAt_eq_one_of_smallLevel` takes exactly this premise
     (`IsOfFinOrder (ρ g)`) together with the fixed level orbit at `U` and the place
     `v`, and gives that the arbitrary element `g` acts trivially on the rational
     `ℓ`-adic Tate module of `B_L`. This is the hypothesis of `hnos` at `W`, `L`, `s`
     and `g`.
3. `hnos` returns an abelian scheme over `Spec V` with generic fibre isomorphic to
   `B`, which is the required good model.

`divisionCMDiscreteValuativeReduction` proves
`DivisionCMDiscreteValuativeReductionStatement …`: at every small level, the good
models of `cmLevelDvrGoodModel_of_division` are turned into the valuative existence
statement by `cmLevelDiscreteValuativeExistence_of_goodModels`.

## Provenance

Internal. The informal counterpart is the projectivity step of Kottwitz, *Points on
some Shimura varieties over finite fields* (1992), §5, printed p. 392 (registered as
`kottwitz-1992-points-shimura-finite-fields`), in characteristic zero. The route
implemented here is: the division algebra excludes a toric part, so the abelian
variety has potentially good reduction; a small level makes the inertia act
trivially on a rational Tate module; the criterion of Néron, Ogg and Shafarevich
gives good reduction; and the polarization, action, Lie condition and level extend
over the valuation ring. The implementation composes the published modules named
above.
