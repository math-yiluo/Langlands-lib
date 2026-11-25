# Normalized valuation of norms in finite separable local extensions

Module `Nyll.ValuedFieldTheory.LocalField.NonarchimedeanLocalField.SeparableNormValuation`, copied unchanged from the Lean library NYLL. The origin of the file is given at the end of this page.

For a finite separable extension `L/K` of nonarchimedean local fields, this file proves the valuation formulas behind finite local reciprocity: `v_K(N x) = f · v_L(x)` for `x ∈ Lˣ` (`N` the norm of `L/K`) and `v_L(x) = e · v_K(x)` for `x ∈ Kˣ`, where `e` and `f` are the ramification index and residue degree of the valuation-ring extension. On the way it proves, for Dedekind domains, Mathlib's formula for the relative norm of a maximal ideal with separability in place of a perfect base.

## Commutative algebra

- `ringNormalClosure_isGalois_of_isSeparable`: for a finite torsion-free extension `R ⊆ S` of domains with separable fraction-field extension, the fraction field of `Ring.NormalClosure R S` is Galois over that of `R`, with no perfectness assumption.
- `relNorm_eq_pow_inertiaDeg_of_isSeparable`: for Dedekind `R ⊆ S` as above and a maximal `P` over a maximal `p`, `Ideal.relNorm R P = p ^ P.inertiaDeg R`.

## Local results

All of these assume compatible valuations (`Valuation.HasExtension`) and finite `L/K`. The first statement and the uniformizer case of the `e`-formula assume `Module.Finite 𝒪[K] 𝒪[L]`; the ideal-norm formula assumes that and separability; every other statement, including `v_mapBaseUnitsToExtensionUnits_eq_ramificationIdx_mul` for general `x ∈ Kˣ`, assumes separability (Galois in the `_of_isGalois` versions) with `IsIntegralClosure 𝒪[L] 𝒪[K] L`.

- `maximalIdeal_map_eq_maximalIdeal_pow_ramificationIdx`: `𝓂[K]·𝒪[L] = 𝓂[L]^e`.
- `relNorm_maximalIdeal_eq_pow_residue_finrank`: `relNorm(𝓂[L]) = 𝓂[K]^f`, with `f = [𝓀[L] : 𝓀[K]]`.
- `v_normUnits_integerRingUniformizerFieldUnit_of_isSeparable` and its inverse version: the norm of the chosen uniformizer of `L` has value `-f`, the norm of its inverse `f`.
- `v_normUnits_eq_residue_finrank_mul_of_isSeparable`: `v_K(N x) = f · v_L(x)`; `_of_isGalois` is the Galois case.
- `v_mapBaseUnitsToExtensionUnits_integerRingUniformizerFieldUnit` (value `-e`) and `v_mapBaseUnitsToExtensionUnits_eq_ramificationIdx_mul`: `v_L(x) = e · v_K(x)` for `x ∈ Kˣ`.
- `valuationMap_comp_normUnits_range_eq_zmultiples_of_isSeparable`: the image of `v_K ∘ N` is `fℤ`; also an `_of_isGalois` version.

## Proofs

The ideal-norm formula passes to the normal closure, where Mathlib's Galois case `Ideal.relNorm_eq_pow_of_isPrime_isGalois` applies, and descends using multiplicativity of `relNorm` in towers. The norm of the uniformizer of `L` generates `relNorm(𝓂[L]) = (π_K^f)`, so it is `π_K^f` times a unit; general `x` are written as a unit times a power of the uniformizer (`uniformizerUnitFactor`, imported). The formula for `e` is the same argument with `𝓂[K]·𝒪[L] = 𝓂[L]^e`.

## Points to watch

- Sign convention: the library's valuation `v` gives the chosen uniformizer the value `-1`, so the uniformizer statements read `-f` and `-e`; the "positive generator" is the inverse uniformizer.
- `e` is Mathlib's `Ideal.ramificationIdx` of `𝓂[L]` over `𝒪[K]`, and `f` is `Module.finrank 𝓀[K] 𝓀[L]`.
- Separability is assumed for the norm formulas and for the general `e`-formula, and the integral-closure property of `𝒪[L]` is a hypothesis, not derived.
- The declarations live in the namespace `LocalClassFieldTheory`.

## Origin of the file

Copied unchanged from the Lean library NYLL (https://github.com/n-yamaguchi-0729/NYLL), commit `fe40c03df1b2b195053fdd63305571d97c73ce48`, file `Nyll/ValuedFieldTheory/LocalField/NonarchimedeanLocalField/SeparableNormValuation.lean`: the Lean file is the source byte for byte (SHA-256 `f84aa2bf4b484ba291f5404fb870e47fee6fd7c1447a6b8f566e08ec82db54c9`). That library is distributed under the Apache License, Version 2.0; its licence and notice are kept with the Library's licences.
