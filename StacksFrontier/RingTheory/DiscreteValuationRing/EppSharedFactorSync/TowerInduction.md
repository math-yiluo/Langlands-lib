# Strong induction for weak solutions of normal towers

Module `StacksFrontier.RingTheory.DiscreteValuationRing.EppSharedFactorSync.TowerInduction`, an extract of the file of the same path of the Lean library AxiomMath/Stacks. The origin of the file and what the extract leaves out are given at the end of this page.

The file reduces the existence of one weak Epp base change for a finite family of towers A → Bᵢ → Cᵢ to the prime-degree family case. The rings and fields lie in a common universe. The base and middle rings are complete, the base residue field is perfect of characteristic p, and the first maps are weakly unramified and satisfy Epp’s condition. The upper fraction-field extensions Mᵢ/Lᵢ are finite and normal.

- `FamilyTowerSolvableAux` asks for one finite extension of the fraction field of A giving weak solutions of all A → Cᵢ. Each member qualifies if A → Cᵢ is already weakly unramified, Mᵢ/Lᵢ is purely inseparable of degree p or Galois of prime degree, or its degree is at most n. `familyTowerSolvable_of_aux` recovers the ordinary statement with the common degree bound.
- `familyTowerSolvable_of_forall_factorFamily` starts at complete towers A → Sᵢ → Cᵢ with Epp’s condition on A → Sᵢ and normal upper degrees at most n₂. Given `hD₁`, weak solutions of all lower extensions over one K₁, and the solver `hnext` at n₂, it gives one finite solution field for the full towers.
- `familyTowerSolvable_of_forall_properNormal` works with compatible finite normal intermediate fields Nᵢ/Lᵢ. It uses `hfirst` for the lower family satisfying the auxiliary alternatives and `hnext` for the upper bound on [Mᵢ : Nᵢ]. A member already weakly unramified or of terminal prime degree may take Nᵢ = Mᵢ, so its upper layer has degree one.
- `familyTowerSolvableAux_all` proves the auxiliary statement at every n. `familyTowerSolvable_all` gives `FamilyTowerSolvable` at every n.

After solving the lower family, the proof pairs each upper reduced tensor factor with the lower factor it extends. Normality and the upper degree bound pass to these extensions. The new family over the integral closure of A in K₁ uses the induction hypothesis once, and the iterated base-change theorem composes the solutions. Proper splits have both degrees smaller by multiplicativity.

Both all-degree results assume `hprime : FamilyPrimeDegreeSolvable p`, which supplies a shared extension for the prime-degree layers.

The comments cite Tag 09F8 for the normal factor induction.

## Origin of the file

Extracted from the Lean library AxiomMath/Stacks (https://github.com/AxiomMath/Stacks), commit `c496df0d9beea9deaeabcea8492605f9a0a2313b`, file `StacksFrontier/RingTheory/DiscreteValuationRing/EppSharedFactorSync/TowerInduction.lean`. That library is distributed under the Apache License, Version 2.0; its licence text is kept with the Library's licences.

Changes made in the extract:

- Every declaration of the source file is kept.
- The import lines are those that the kept text needs.
- The library's Lean options that differ from Lean's defaults are set at the top of the file (`autoImplicit false`, `maxSynthPendingDepth 3`).
