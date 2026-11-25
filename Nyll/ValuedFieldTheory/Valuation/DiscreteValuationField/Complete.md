# Complete discretely valued fields

Module `Nyll.ValuedFieldTheory.Valuation.DiscreteValuationField.Complete`, copied unchanged from the Lean library NYLL. The origin of the file is given at the end of this page.

The file defines complete discrete valuations and the library's structure of a complete discretely valued field, shows that the valuation ring is Henselian, and restates the basic facts about uniformizers and powers of the maximal ideal in this setting.

## Main definitions

- `Valuation.IsCompleteDiscrete val`: a class saying that the valuation `val` is discrete of rank one and that its valuation ring `O` is complete and separated for the `𝔪`-adic topology (`IsAdicComplete`).
- `CompleteDVF K`: a structure bundling a value group, a valuation on `K` and an `IsCompleteDiscrete` instance. `toHenselianDVF` and `toDVF` forget to the library's `HenselianDVF` and `DVF`; `valuationSubring`, `maximalIdeal`, `residueField`, `residueMap` are taken from there.

## Main results

- `Valuation.henselianRing`, `CompleteDVF.henselianRing`: the valuation ring of a complete discrete valuation is a Henselian local ring (Mathlib's instance for adically complete rings).
- `isCompleteDiscrete_comap_ringEquiv`: pulling back along a field isomorphism keeps the valuation complete and discrete.
- `mem_maximalIdeal_pow_iff_valuation_le_uniformizer_pow`: `x ∈ 𝔪ⁿ` if and only if `v x ≤ v(ϖⁿ)`, for any rank-one discrete valuation.
- `principalAdicComplete_of_ne_zero_mem_maximalIdeal`: for any nonzero `π ∈ 𝔪`, `O` is complete for the `π`-adic topology, since `(π) = 𝔪ⁿ` with `n > 0` (with the precomplete and Hausdorff parts stated separately).
- `eq_zero_of_mem_maximalIdeal_pow_all`: an element lying in every `𝔪ⁿ` is zero; `unit_eq_of_idealQuotient_eq_all`: two units of `O` with the same image in every `O/𝔪ⁿ` are equal.
- Restatements through `toDVF`: existence of uniformizers, `𝔪 = (ϖ)`, `𝔪ⁿ = (ϖⁿ)`, `ϖ ∉ 𝔪²`, `𝔪 ≠ ⊥`, nonzero ideals are powers of `𝔪`, residue characterizations.

## Points to watch

Completeness here means `𝔪`-adic completeness of the valuation ring, not completeness of `K` for a metric or uniform structure. `CompleteDVF` is the library's own structure with the valuation as data, not a Mathlib class.

## Origin of the file

Copied unchanged from the Lean library NYLL (https://github.com/n-yamaguchi-0729/NYLL), commit `fe40c03df1b2b195053fdd63305571d97c73ce48`, file `Nyll/ValuedFieldTheory/Valuation/DiscreteValuationField/Complete.lean`: the Lean file is the source byte for byte (SHA-256 `e51c4e46f9e569325c1e99e7a980660e0960d17e04db11bb050e9224666849e7`). That library is distributed under the Apache License, Version 2.0; its licence and notice are kept with the Library's licences.
