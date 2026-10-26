# Rank zero of actual refined cuspidal induction

Author: Worker 717.

This module proves the conclusion of the published proposition
`Langlands.CuspidalSupport.RefinedCuspidalInductionFiniteLengthStatement`
from [`RefinedCuspidalInductionLengthStatement`](RefinedCuspidalInductionLengthStatement.md)
in total rank `n = 0`. It does not prove that proposition, whose positive
ranks remain open here. It also contains two general lemmas: admissible
representations of a trivial group have finite length, and finite length over
the group algebra yields an actual composition series. The second one is
needed in every rank.

The field universe `uF` and the representation universe `uV` are independent
throughout, as in the target.

## Declarations

In namespace `Langlands`, for a field `k`, a group `G` and a `k`-module `V`:

- `finite_of_isAdmissible_of_subsingleton`: if `G` is a topological group
  with at most one element and `ρ : Representation k G V` is admissible
  (`IsAdmissible ρ`), then `V` is finite-dimensional over `k`
  (`Module.Finite k V`).
- `isFiniteLength_of_isAdmissible_of_subsingleton`: under the same
  hypotheses, `ρ.asModule` has finite length over `MonoidAlgebra k G`.
- `exists_hasCompositionSeriesLength_of_isFiniteLength A h`: for any group `G`
  (no topology) and any `A : Rep.{uV} k G` whose module `A.ρ.asModule` has
  finite length over `MonoidAlgebra k G`, there is `m : ℕ` with
  `HasCompositionSeriesLength A m`, the project's actual composition series of
  subrepresentations with irreducible successive quotients.

In namespace `Langlands.CuspidalSupport`:

- `refinedCuspidalInductionFiniteLength_rankZero F T B S ω`: for a prime `p`,
  `F : PadicField.{uF} p`, `T : F.TopologicalData`, `B : BlockShape 0`,
  `S : BlockRefinement B` and `ω : Rep.{uV} ℂ ((B.flatten S).Levi F.Carrier)`
  with `IsLeviCuspidal (B.flatten S) ω.ρ`, put
  `σ = ω.ρ.comp (flattenedLeviEquiv F.Carrier B S).symm.toMonoidHom` and
  `I = Rep.of (T.normalizedRefinedInduced B S σ) : Rep.{max uF uV} ℂ (B.Levi F.Carrier)`.
  Then `I.ρ` is admissible, `I.ρ.asModule` has finite length over
  `MonoidAlgebra ℂ (B.Levi F.Carrier)`, and `HasCompositionSeriesLength I m`
  holds for some `m`. The topologies are `T.topology` and
  `T.leviTopologicalGroup B`. This is the conclusion of the target, with the
  same transport, induced object and `Rep.of` packaging. The irreducibility
  hypothesis of the target is not needed in rank zero, so it is omitted.
- `RefinedCuspidalInductionRankZeroClause` is the record's named definition.
  It is a proposition (`Prop`) with universe parameters `uF` and `uV`. It says
  that the previous item holds for every prime `p`, every `F`, every `T`,
  every `B : BlockShape 0`, every `S` and every `ω` with
  `IsLeviCuspidal (B.flatten S) ω.ρ`. It is the target proposition restricted to
  `n = 0` with the hypothesis `Representation.IsIrreducible ω.ρ` deleted.
- `refinedCuspidalInductionRankZeroClause_holds` proves this clause.

## Implemented proof

1. `finite_of_isAdmissible_of_subsingleton`. Admissibility gives finite
   dimensionality of the fixed vectors of every open subgroup. Apply this to the
   open subgroup `⊤`. Because `G` has only the element `1`, every vector is
   fixed by `⊤`. So the fixed-vector submodule is `⊤`, and `V` is
   finite-dimensional via `Submodule.topEquiv`.
2. `isFiniteLength_of_isAdmissible_of_subsingleton`. `MonoidAlgebra k G`
   is a `k`-algebra, and `ρ.asModule` is a finite-dimensional `k`-module. By
   the tower lemmas `isNoetherian_of_tower` and `isArtinian_of_tower`, it is
   Noetherian and Artinian over the group algebra. Mathlib's
   `isFiniteLength_iff_isNoetherian_isArtinian` then gives finite length.
3. `exists_hasCompositionSeriesLength_of_isFiniteLength`. Mathlib's
   `isFiniteLength_iff_exists_compositionSeries` gives a composition series of
   submodules from `⊥` to `⊤`. The published
   `Filtration.LengthCriterionProof.hasCompositionSeriesLength_of_compositionSeries`
   converts it into `HasCompositionSeriesLength A s.length`.
4. `refinedCuspidalInductionFiniteLength_rankZero`. A block shape of total
   rank `0` has no blocks: a block `i` would contain the position
   `⟨i, 0⟩` (`B.positive i`), and `B.indexEquiv` would send it to an element of
   `Fin 0`. So `Fin B.length` is empty. The product Levi `B.Levi F.Carrier` is
   then a subsingleton. Admissibility of `I.ρ` is the published theorem
   `Parabolic.refinedCuspidalInduction_isAdmissible` from
   [`RefinedInductionAdmissibility`](../Parabolic/RefinedInductionAdmissibility.md),
   which uses only `IsLeviCuspidal`. Steps 2 and 3 then give finite length and a
   composition series.

The same `I` is used throughout, so the result concerns the actual normalized
refined induction with right translation and positive half-modulus
normalization. No finite-dimensionality, finite generation or chosen series
is assumed.

## Provenance

Internal. The rank-zero case is a degenerate case of the target, whose
motivation is recorded in the target's Markdown. The general lemmas are
elementary consequences of Mathlib's finite-length theory and the project's
published composition-series bridge, so there is no specific source statement
to translate.
