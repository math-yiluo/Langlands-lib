# The degree formula n = e·f for extensions of complete discretely valued fields

Module `Nyll.ValuedFieldTheory.Valuation.DiscreteValuationField.FiniteExtension.Degree`, copied unchanged from the Lean library NYLL. The origin of the file is given at the end of this page.

Let `L / K` be a finite extension, and `base`, `target` complete discretely valued fields on `K` and `L` (the library's `CompleteDVF`) with the valuation of `target` extending that of `base`. The file proves the local identity `[L : K] = e · f` under several hypotheses making `O_L` the integral closure of `O_K`, or a finite `O_K`-module, and proves positivity of `e` and `f`.

## Main results

- `idealOfLE_eq_maximalIdeal_of_isIntegral` (and `_of_finite`): for valuation subrings `R ≤ S` of a field with `R → S` integral (or finite), the center of `S` on `R` is the maximal ideal of `R`. `mem_maximalIdeal_of_map_mem_maximalIdeal`: any ring map between local rings reflects membership in the maximal ideal.
- `ideal_ramificationIdx_mul_inertiaDeg_eq_finrank_of_hasExtension`, `ramificationIndex_mul_residueDegree_eq_degree`: `e · f = [L : K]` when `O_L` is a finite `O_K`-module.
- `ideal_ramificationIdx_mul_inertiaDeg_eq_finrank_of_isIntegralClosure`, `isDefectless_of_isIntegralClosure`, `ramificationIndex_mul_residueDegree_eq_degree_of_isIntegralClosure`: the same for `L / K` separable when `O_L` is the integral closure of `O_K` in `L` (it is then module-finite).
- Under the hypothesis `hval` (each `z ∈ L` or its inverse is integral over `O_K`), the integral closure is a valuation subring `B ≤ O_L`. If, moreover, the inclusion `B → O_L` is local, or integral, or the center of `O_L` on `B` is the maximal ideal, then `O_L` is the integral closure; for `L / K` separable, `O_L` is then module-finite and `e · f = [L : K]`, one theorem per combination.
- For `B` as above: the map `O_K → B` is injective, the center of any extension on `B` contracts to `𝔪_K`, and for `L / K` separable the only prime of `B` over `𝔪_K` is its maximal ideal.
- `residueDegree_eq_finrank_quotient`: `f` is the dimension of `O_L/𝔪_L` over `O_K/𝔪_K`. `residueDegree_pos`, `residueField_finiteDimensional_of_moduleFinite`: if `O_L` is module-finite, `f > 0` and the residue extension is finite. `ramificationIndex_ne_zero`: `e ≠ 0` when `O_L` is torsion-free over `O_K`.

## Proof

Each variant reduces to the library's theorem that a module-finite extension of valuation rings has no defect, which applies Mathlib's formula `∑ e_P f_P = [L : K]` with a single prime `P`.

## Points to watch

- Completeness is not used to derive the hypotheses: every form of `e · f = [L : K]` here assumes module-finiteness of `O_L`, or that `O_L` is the integral closure, or `hval` together with a condition on the inclusion `B → O_L`. These hypotheses stand for the step "the extended valuation ring is the integral closure", which this file does not prove. Each form also takes the instance `IsScalarTower O_K O_L L`.
- `ramificationIndex` is Mathlib's `Ideal.ramificationIdx'` and `residueDegree` is `inertiaDeg`, through the library's `ValuedExtension` definitions applied to `toDVF`.

## Origin of the file

Copied unchanged from the Lean library NYLL (https://github.com/n-yamaguchi-0729/NYLL), commit `fe40c03df1b2b195053fdd63305571d97c73ce48`, file `Nyll/ValuedFieldTheory/Valuation/DiscreteValuationField/FiniteExtension/Degree.lean`: the Lean file is the source byte for byte (SHA-256 `6d783468d3a5299e4aa0bf9ade46a6b1604bd30a3920b5a5b5766f16e966b9b3`). That library is distributed under the Apache License, Version 2.0; its licence and notice are kept with the Library's licences.
