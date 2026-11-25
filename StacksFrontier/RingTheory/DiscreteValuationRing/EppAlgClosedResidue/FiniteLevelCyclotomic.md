# Normal field factors of a base-changed tower

Module `StacksFrontier.RingTheory.DiscreteValuationRing.EppAlgClosedResidue.FiniteLevelCyclotomic`, an extract of the file of the same path of the Lean library AxiomMath/Stacks. The origin of the file and what the extract leaves out are given at the end of this page.

The file shows how normality and a degree bound pass from a finite normal extension M/L to the matching field factors after a base change, and proves two auxiliary facts on local extensions in mixed characteristic.

## Results

- `exists_fieldFactor_normal_and_finrank_le` assumes M/L finite normal, in a tower K → L → M, with a field N over K. Given an N-algebra equivalence from the reduction of L ⊗[K] N to a finite product of fields Hᵢ, compatible with L, and a surjective N-algebra map φ from M ⊗[K] N onto a field F with φ(m ⊗ n) = m·n, it finds a factor Hᵢ and an N-map Hᵢ → F over L with F/Hᵢ finite normal and [F : Hᵢ] ≤ [M : L].
- `normal_and_finrank_le_of_surjective_tensorProduct`: if E/F is finite normal and the map K ⊗[F] E → L induced by a compatible square of fields is surjective, then L/K is finite normal and [L : K] ≤ [E : F].
- `AlgHom.exists_comp_evalAlgHom_eq`: an R-algebra map from a finite product of R-algebras to a domain factors through one projection.
- `ramificationIdx_dvd_finrank_of_isLocalRing`: for a finite flat local homomorphism R → S of local rings, R a domain, the ramification index of the maximal ideal of S divides the rank of S over R.
- `exists_irreducible_associated_pow_wElt`: for a discrete valuation ring B of characteristic zero with residue characteristic p and a ring map f from the p-th cyclotomic ring over ℤ to B, the element `wElt f` = 1 − ζ, where ζ is the image of the primitive p-th root of unity, is associated to πᵉ for a uniformizer π and some e > 0.

For the factor result, the map from the reduction of L ⊗[K] N to F through M ⊗[K] N factors through one Hᵢ, and the resulting surjection Hᵢ ⊗[L] M → F gives normality and the degree bound. The divisibility comes from the formula Σ eᵢfᵢ = rank with a single prime above the maximal ideal of R.

## Points to watch

- The bound on factor degrees is non-strict.
- The module docstring announces the finite-level induction and the Galois case over a cyclotomic field; neither is in the file.

## Origin of the file

Extracted from the Lean library AxiomMath/Stacks (https://github.com/AxiomMath/Stacks), commit `c496df0d9beea9deaeabcea8492605f9a0a2313b`, file `StacksFrontier/RingTheory/DiscreteValuationRing/EppAlgClosedResidue/FiniteLevelCyclotomic.lean`. That library is distributed under the Apache License, Version 2.0; its licence text is kept with the Library's licences.

Changes made in the extract:

- Of the 13 declarations of the source file 5 are kept. The 8 left out are not needed by the results for which the extract is made: `IsDiscreteValuationRing.FiniteLevelSolvable`, `IsDiscreteValuationRing.NormalTowerSolvable`, `IsDiscreteValuationRing.charP_of_algebra_field`, `IsDiscreteValuationRing.charZero_of_algebra_field`, `IsDiscreteValuationRing.exists_finite_extension_isWeakSolution_of_finiteLevel_of_perfectResidue`, `IsDiscreteValuationRing.exists_finite_extension_isWeakSolution_of_isGalois_of_cyclotomic_of_perfectResidue`, `IsDiscreteValuationRing.exists_finite_extension_isWeakSolution_of_normal_factor_induction_of_cyclotomic_extension`, `IsDiscreteValuationRing.finiteLevelSolvable`.
- The import lines are those that the kept text needs.
- The library's Lean options that differ from Lean's defaults are set at the top of the file (`autoImplicit false`, `maxSynthPendingDepth 3`).
- The import of the library's own attribute modules is replaced by `Mathlib.Tactic.CrossRefAttribute`.
