# Reduction of fixed-level finiteness on `G°`

This module proves that two prerequisite propositions together imply the
published proposition `Langlands.CuspidalSupport.CompactCoefficientFixedLevelFinitenessTheorem.{uF, uV}`
(Bernstein--Zelevinsky (1976), Theorem 4.14, page 41, in its compact-open form).
The two prerequisites are:

- `Langlands.CuspidalSupport.DeterminantUnitCornerStructureStatement.{uF}`, the
  sandwich structure of compact-open Hecke corners of `G°` (BZ76 Lemma 4.9);
- `Langlands.SandwichSimpleModuleDimensionBoundStatement.{uF, uV}`, the
  dimension bound for finite-dimensional simple modules over sandwich algebras
  (BZ76 Lemma 4.10 and §4.11).

The reduction is the argument of BZ76 4.16. The theorem takes both
prerequisites as hypotheses and proves nothing about them.

## Declarations

- `CompactCoefficientClass.fixedStratum_mono`: for subgroups `N ≤ K`, every
  class with a nonzero `K`-fixed vector has a nonzero `N`-fixed vector. On a
  representative, `K`-fixed vectors are `N`-fixed.
- `CuspidalSupport.compactCoefficientFixedLevelFiniteness_of_cornerStructure hA hB`
  proves `CompactCoefficientFixedLevelFinitenessTheorem.{uF, uV}` from `hA` and
  `hB`.

## Proof

1. Fix `p`, `F`, `T`, `n`, `B` and a compact open subgroup `K` of
   `G° = determinantUnitSubgroup T B`. Install the topology `T.topology`, the
   topological group instance `T.leviTopologicalGroup B`, and the Borel
   measurable structure.
2. `hA` gives a compact open `N ≤ K` with a sandwich structure of
   `HeckeAlgebra.Corner μ N hN` for every Haar measure `μ`.
3. Take `μ = Measure.haarMeasure K₀`. Here `K₀` is `K` as a positive compact
   set: it is compact by hypothesis, and its interior is `K`, which contains
   `1`.
4. `fixedStratum_finite_of_sandwich` (module
   `Langlands.Representation.CompactCoefficient.FixedLevelFiniteness`) shows
   that the `N`-stratum is finite.
5. The `K`-stratum is contained in the `N`-stratum, by `fixedStratum_mono`.

The positive-rank hypothesis `0 < n` of the target is not used.
