# The cup product on the cohomology of a topological group

`Langlands/Cohomology/Profinite/Cup/Basic.lean`, namespace `Langlands.ProfiniteCohomology`.

The cup product of locally constant cochains is locally constant, satisfies the Leibniz rule, and
so descends to cohomology: `cup h : Hᵖ(G, A) →ₗ H^q(G, B) →ₗ Hⁿ(G, A ⊗ B)` for `h : p + q = n`. The
unit class in `H⁰(G, k)` is a unit for it.

## Declarations

- `isLocallyConstant_cupCochain`, `cupCochain_zero_left`, `cupCochain_zero_right`.
- `cochainOf`, `mkCochain` and their lemmas (`cochainOf_mkCochain`, `isLocallyConstant_cochainOf`,
  `cochainOf_injective`, `cochainOf_add`, `cochainOf_smul`, `cochainOf_zero`, `cochainOf_d`): passage
  between elements of the complex `cochains A` and functions.
- `cupLocallyConstant`, `cochainOf_cupLocallyConstant`: the cup product on locally constant cochains.
- `cocycleι`, `cocycleι_injective`, `d_cocycleι`, `cochainOf_cocycleι_toCycles`, `cocycles_ext`:
  cocycles as cochains.
- `isCocycle_cupCochain`, `cupCocyclesAlt`, `cocycle_inclusion_cupCocycles`, `cupCocycles`,
  `cocycleι_cupCocycles`, `cupCocycles_toCycles_left`, `cupCocycles_toCycles_right`: the cup product of
  cocycles, and the cup product of a coboundary with a cocycle is a coboundary.
- `cohomologyπ_surjective`, `cohomologyπ_toCycles`, `cohomology_linearMap_ext`, `cocyclesHom`,
  `toCycles_cocyclesHom`, `descCohomologyHom`, `π_descCohomologyHom`, `descCohomology`,
  `descCohomology_cohomologyπ`, `cohomology_induction_on`: describing maps out of cohomology by
  cocycles.
- `cupCocyclesπ` and its lemmas, `cupProductCocycleClass`, `cup_cohomology_class`; `cup h` and
  `cup_cohomologyπ`: the cup product on cohomology, computed on classes of cocycles.
- `cochainOf_cocycleι_cyclesMap`, `cohomologyMap_cohomologyπ`, `cochainOf_cocycleι_cocyclesMap`,
  `map_cohomologyπ`: coefficient maps and maps along group homomorphisms on classes.
- `d_oneCochain`, `unitCocycle`, `unitClass` (the class of `1` in `H⁰(G, k)`);
  `cohomologyMap_leftUnitor_unitClass_cup`, `cohomologyMap_rightUnitor_cup_unitClass`: `1 ∪ x = x` and
  `x ∪ 1 = x` through the unitors.

## Source and licence

Ported from `src/GroundTheory/ProfiniteCohomology/CupProducts.lean`, `CupProducts/Cocycles.lean` and
`CupProducts/CohomologyMapRightUnitorCupUnitClass.lean` of the repository `leanprover-community/riemann-hypothesis` (<https://github.com/leanprover-community/riemann-hypothesis>), commit `f1f6d65`. The repository has no licence file; its text is used with attribution (`licenses/RiemannHypothesis/SOURCE.md`). Names are the source's; the instance for
tensor products and its stabilizer lemma moved to `SmoothCoefficients.lean`; coefficient maps are
`coeffMap` (the source's `cohomologyMap`).

## References

- J. Neukirch, A. Schmidt, K. Wingberg, *Cohomology of Number Fields*, 2nd edition (Springer 2008;
  corrected printing 2013), chapter I, §4, pp. 36–37 (the cup product of cochains, Proposition
  (1.4.1), and the cup product on cohomology).
- J.-P. Serre, *Galois Cohomology* (English translation of *Cohomologie galoisienne*, Springer 1997;
  corrected printing 2002), chapter I, §2.6 a), p. 15 (cup products; Serre leaves their properties
  to the reader).
