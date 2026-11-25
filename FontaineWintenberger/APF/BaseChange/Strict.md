# Strictly APF extensions under a finite change of base

Module `FontaineWintenberger.APF.BaseChange.Strict`, copied from the Lean library FontaineWintenberger. The origin of the file and the changes made in the copy are given at the end of this page.

The file proves that strict arithmetic profiniteness of a separable extension `N/K` is unchanged when the base `K`, complete discretely valued with perfect residue field, is replaced by a finite separable extension `M` contained in `N`. First for `M` an intermediate field of `SeparableClosure K`, then for an abstract normed field `M`, restating there the base change of `IsAPF`, the index and `ψ = apfPsi`.

## Finite base inside the separable closure

- `IsAPF.liminf_comp_apfPsi`: for an APF extension `L/K` and `f : ℝ → ℝ≥0∞`, the lower limit at infinity of `f ∘ apfPsi K L` equals that of `f`.
- `IsAPF.apfStrictnessRatio_finiteBase`: for `N/K` APF and `u ≥ 0`, `apfStrictnessRatio M N (apfPsi K M u) = apfIndex K M u * apfStrictnessRatio K N u`.
- `IsAPF.exists_liminf_finiteBase_mul`: the lower limits of the strictness ratios of `N/M` and `N/K` differ by a positive natural factor.
- `isStrictlyAPF_finiteBase_iff`: `IsStrictlyAPF K N ↔ IsStrictlyAPF M N`.

## Abstract finite base with a chosen embedding

The namespace `AbstractFiniteBase` treats a finite separable extension `M/K` given as a type, with an algebra structure `M → SeparableClosure K` and, for the valued statements, a norm making it complete discretely valued with perfect residue field. It repeats the construction of the earlier modules: `closureEquiv` (an isomorphism `SeparableClosure M ≃ SeparableClosure K` over `M`), `closureHom : G_M → G_K` with range the fixing subgroup of the image of `M`, `rebaseFiniteGaloisLayer` with the cofinality statement `exists_layer`, `comap_upper` (the preimage of `G_K^u` is `G_M^v`, `v = apfPsi K M u`, `u ≥ -1`), `embedding`, `comap_apf`, then `isAPF_iff`, `index_mul`, `psi_comp`, `ratio`, `exists_liminf_mul` and `isStrictlyAPF_iff`.

## Abstract normed base

For a nontrivially normed ultrametric field `M` with `NormedAlgebra K M`, finite and separable over `K`, and `N` over `M` separable over `K`:

- `isAPF_finiteBase_iff_of_normedAlgebra`: `IsAPF K N ↔ IsAPF M N`;
- `apfIndex_eq_mul_finiteBase_of_normedAlgebra`: `apfIndex K N u = apfIndex K M u * apfIndex M N (apfPsi K M u)` for `u ≥ 0`;
- `IsAPF.apfPsi_finiteBase_comp_of_normedAlgebra`: `apfPsi M N ∘ apfPsi K M = apfPsi K N` for `N/K` APF;
- `IsAPF.apfStrictnessRatio_finiteBase_of_normedAlgebra`;
- `isStrictlyAPF_finiteBase_iff_of_normedAlgebra`: `IsStrictlyAPF K N ↔ IsStrictlyAPF M N`.

## Proofs

The index of the finite extension `M/K` is eventually constant (`exists_apfIndex_finite_constant`), so the two lower limits differ by that constant.

## What to watch for

- `IsStrictlyAPF` and `apfStrictnessRatio` are defined elsewhere.
- In the last five statements the discrete valuation structure on `M` and the separability of `N/M` are supplied by `letI` inside the statement, and the embedding of `M` into `SeparableClosure K` is chosen in the proof.

## References

Wintenberger, *Le corps des normes de certaines extensions infinies de corps locaux; applications*, §1.

## Origin of the file

Copied from the Lean library FontaineWintenberger (https://github.com/YijunYuan/FontaineWintenberger), commit `e835d58871d8d564901c0f13b685034cd202659e`, file `FontaineWintenberger/APF/BaseChange/Strict.lean` (SHA-256 of the source file `519ad0870f0e407212aebb707a60f2fe2b0161644b9cc4d765b87051253a4b52`). That library is distributed under the Apache License, Version 2.0; its licence text is kept with the Library's licences.

Changes made in the copy:

- The two Lean options that the library's lakefile sets and that differ from Lean's defaults are set after the imports (`relaxedAutoImplicit false`, `maxSynthPendingDepth 3`).
