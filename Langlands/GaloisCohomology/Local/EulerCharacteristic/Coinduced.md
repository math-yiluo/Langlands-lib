# Vanishing criteria and the Euler characteristic of coinduced modules

`Langlands/GaloisCohomology/Local/EulerCharacteristic/Coinduced.lean`, namespace `Langlands.ProfiniteCohomology`.

Two tools for the local Euler characteristic. First, vanishing: if an open normal subgroup acts
trivially on `A`, conjugation acts trivially on the cohomology of a module `T`, and `A` is a sum of
copies of `T` up to an invertible index, then `Hⁿ(A) = 0` (`subsingleton_cohomology_of_sum`); and
cohomology vanishes for a module with no invariants under a closed normal subgroup whose
cohomology vanishes (`subsingleton_cohomology_of_normal`). Second, for an open normal subgroup `H`
with cyclic quotient of order `pᵃ` and a finite `p`-torsion module `M`,
`χ(H, M) = χ(G, M)^{pᵃ}` (`eulerCharacteristic_res_eq_pow`), computed on the coinduced module
`Coind_H^G M` by a filtration with graded pieces isomorphic to `M`.

## Declarations

- `resTrivMor`, `cohomologyMap_comp_cohomologyConj_of_apply`, `cohomologyConj_eq_cohomologyMap_of_sum`,
  `subsingleton_cohomology_of_cohomologyConj_eq`, `subsingleton_cohomology_of_sum`,
  `subsingleton_cohomology_of_normal`.
- `eulerCharacteristic_eq_of_iso`, `eulerCharacteristic_eq_one_of_subsingleton`.
- `coindRes H M` (`Coind_H^G Res M`), `coindShift` (the action of a generator of `G/H`),
  `rangeStepComplex`, `eulerCharacteristic_rangeStep`, `coindResConst`, `kerShiftEquiv`,
  `coindOfFun`, `card_pow_le_card_coindRes`.
- `eulerCharacteristic_coind_res_eq_pow`, `eulerCharacteristic_res_eq_pow`.

## Source and licence

Ported from the repository `leanprover-community/riemann-hypothesis` (<https://github.com/leanprover-community/riemann-hypothesis>), commit `f1f6d65`, files `src/GroundTheory/ProfiniteCohomology/LocalEulerCharacteristic/VanishingCore.lean` and `MainCoind.lean`. Mechanical renames (as in the foundations, `Langlands/Cohomology/Profinite/`): `IsDiscreteRep` → `IsSmoothRep`, `cohomologyMap` → `coeffMap`, `cohomologyMapAlong φ hφ` → `map ⟨φ, hφ⟩`, `cochainsComplex` → `cochains`, `cohomologyRes/Cores/ResLE` → `res/cores/resOfLE`, `H0Iso` → `zeroIso`, `eulerChar` → `eulerCharacteristic` (also inside names), `galUnits`/`galRootsOfUnity` → `unitsModule`/`rootsOfUnityModule` (lemma names keep `galUnits`/`galRootsOfUnity`), `unitsIncl` → `integerUnitsMap`. The repository has no licence file; its text is used with attribution (`licenses/RiemannHypothesis/SOURCE.md`).

## References

- J. Tate, *Duality theorems in Galois cohomology over number fields*, Proc. Internat. Congr.
  Mathematicians (Stockholm, 1962), 288–295, §2, Theorem 2.2 and the sketch of its proof, p. 289
  (the local Euler characteristic formula, for `k` complete under a discrete valuation with finite
  residue field and `|M|` invertible in `k`, §1, p. 288).
- J. Neukirch, A. Schmidt, K. Wingberg, *Cohomology of Number Fields*, chapter VII, §3, Theorem
  (7.3.1) and its proof, pp. 392–396.
- J.-P. Serre, *Galois Cohomology*, chapter II, §5.7, Theorem 5 and its proof (for `p`-adic fields),
  pp. 99–101.
