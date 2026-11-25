# Prime-degree layers and normal intermediate fields

Module `StacksFrontier.RingTheory.DiscreteValuationRing.EppSharedFactorSync.TowerLevels`, an extract of the file of the same path of the Lean library AxiomMath/Stacks. The origin of the file and what the extract leaves out are given at the end of this page.

The file analyzes which upper layers in a family of discrete valuation ring towers A → Bᵢ → Cᵢ can be handled directly and which can be split. A layer M/L is terminal when it is purely inseparable of degree p or Galois of prime degree.

- `familyTowerSolvable_of_forall_terminal_or_isWeaklyUnramified` gives a single finite extension of K producing weak solutions for the full family when every member either has A → Cᵢ already weakly unramified or a terminal upper layer. The family has a finite index type in the same universe as the rings and fields, complete A and Bᵢ, and perfect residue field of characteristic p at A; the first maps are weakly unramified and satisfy Epp’s condition, and the upper fraction-field extensions are finite and normal.
- `isWeaklyUnramified_or_terminal_or_exists_properNormal` gives three alternatives for a single finite normal upper layer M/L. Either A → C is weakly unramified, M/L is terminal, or there is a normal intermediate E/L with both degrees greater than one. It assumes B complete, A → B weakly unramified, and residue characteristic p at A.

The family proof uses `hprime : FamilyPrimeDegreeSolvable p` to construct one extension for the members that are not weakly unramified. Over the perfect base residue field, that extension also serves the members that are. The trichotomy uses the separable closure and, in the Galois case, the fixed field of inertia: a full inertia group makes the Galois group solvable and the degree prime, a trivial one makes B → C formally unramified. The private `exists_isPurelyInseparable_finrank_eq` supplies a purely inseparable intermediate field of degree p, and `charZero_or_charP_of_isFractionRing` the characteristic of L.

The disjunction permits overlapping alternatives and establishes only the case split used in the tower proof. The family theorem takes the prime-degree solver `hprime` as an input. The module docstring, and the docstring of the family theorem, refer to further results on terminal layers that the file does not contain.

The comments cite Tag 09F8 for the normal-layer case split.

## Origin of the file

Extracted from the Lean library AxiomMath/Stacks (https://github.com/AxiomMath/Stacks), commit `c496df0d9beea9deaeabcea8492605f9a0a2313b`, file `StacksFrontier/RingTheory/DiscreteValuationRing/EppSharedFactorSync/TowerLevels.lean`. That library is distributed under the Apache License, Version 2.0; its licence text is kept with the Library's licences.

Changes made in the extract:

- Of the 9 declarations of the source file 4 are kept. The 5 left out are not needed by the results for which the extract is made: `Stacks.EppTheorem.exists_terminal_bottomLayer`, `Stacks.EppTheorem.familyTowerSolvable_mono`, `Stacks.EppTheorem.familyTowerSolvable_of_forall_finrank_prime`, `Stacks.EppTheorem.familyTowerSolvable_of_forall_terminal`, `Stacks.EppTheorem.terminal_of_normal_of_finrank_prime`.
- The import lines are those that the kept text needs.
- The library's Lean options that differ from Lean's defaults are set at the top of the file (`autoImplicit false`, `maxSynthPendingDepth 3`).
