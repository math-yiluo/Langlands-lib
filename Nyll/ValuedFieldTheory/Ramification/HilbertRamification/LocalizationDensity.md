# Density of L in its localization and transport of inertia and ramification

Module `Nyll.ValuedFieldTheory.Ramification.HilbertRamification.LocalizationDensity`, copied unchanged from the Lean library NYLL. The origin of the file is given at the end of this page.

Let K be a field with a real absolute value v_K, L/K an extension, and w an extension of v_K to L (`AbsoluteValueExtension vK L`). The field L_w attached to w is taken to be the algebraic localization L·K_v, an intermediate field between the completion K_v and the completion of L, not the whole completion of L. The file shows that L is dense in L·K_v and uses this to carry inertia and ramification conditions from L to L·K_v. Finite degree is never assumed.

## Definitions

`localization vK w` is the algebraic localization, `toLocalization vK w` the embedding L → L·K_v, and `localizationAbsoluteValue vK w` its absolute value. For nonarchimedean w, `extensionValuationSubring` and `localizationValuationSubring` are the valuation subrings of L and of L·K_v.

## Results

- For a nonarchimedean absolute value, the nonunits of its valuation subring are the elements with |x| < 1, and the principal units are the units with |u − 1| < 1.
- `algebraicLocalizationDensity_localization_exists_close`: every element of L·K_v is within any ε > 0 of an element of L.
- Nonarchimedeanness passes from w to L·K_v, and the valuation subring of L·K_v pulls back to that of L.
- `algebraicLocalizationDensity_localizationAbsoluteValue_algEquiv`: if L/K is algebraic and v_K nontrivial, every K_v-automorphism of L·K_v preserves its absolute value.
- Every integral element of L·K_v is within distance less than 1 of an integral element of L. The map Lˣ/U¹ → (L·K_v)ˣ/U¹ is surjective, and principal units of L go to principal units.
- `algebraicLocalizationDensity_localization_mem_inertia_of_commutes`: let τ be in the decomposition group of L·K_v over K_v and σ in that of L over K, with τ ∘ j = j ∘ σ for the embedding j. If σ is in the inertia group, so is τ.
- `algebraicLocalizationDensity_localization_mem_ramification_of_commutes`: in the same situation, with τ and σ in the inertia groups, if σ is in the ramification group, so is τ.

Both transport theorems assume L/K algebraic, v_K nontrivial and w nonarchimedean.

## Proof

Approximation comes from the dense range of L in its completion. Every element is an approximation from L plus a small error, τ is an isometry, and the strong triangle inequality bounds the result. For ramification, a unit is factored as a principal unit times a unit of L.

## Watch for

- Only one direction of each comparison is proved, from L to L·K_v. The compatibility of τ and σ is the hypothesis `hcomm`, not constructed here.
- Nonarchimedean means the library's `LubinTate.Valuations.NonarchimedeanAbsoluteValue`, defined by boundedness on the natural numbers.

## Origin of the file

Copied unchanged from the Lean library NYLL (https://github.com/n-yamaguchi-0729/NYLL), commit `fe40c03df1b2b195053fdd63305571d97c73ce48`, file `Nyll/ValuedFieldTheory/Ramification/HilbertRamification/LocalizationDensity.lean`: the Lean file is the source byte for byte (SHA-256 `011af1063960daefa02170b20b54974cfb144f281e499ae42ffaa58220195ff4`). That library is distributed under the Apache License, Version 2.0; its licence and notice are kept with the Library's licences.
