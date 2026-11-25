# Ramification numbers of valuation-preserving automorphisms

Module `FontaineWintenberger.Ramification.Embedding.Valued`, copied from the Lean library FontaineWintenberger. The origin of the file and the changes made in the copy are given at the end of this page.

The file attaches a ramification number to an automorphism `g` of a field `F` preserving a valuation `v` with discrete valuation ring, and computes it on a uniformizer. Neither completeness, a finite residue field, nor finite order of `g` is assumed.

## Definitions

- `integerRamificationNumber g : EReal`, for a ring automorphism `g` of a discrete valuation ring `R`: the value `ramificationOrder (R := R) (R ≃+* R) g` minus `1`.
- `valuationIntegerAut v g hv`: the automorphism of `v.valuationSubring` induced by `g`, given `hv : ∀ x, v (g x) = v x`.
- `valuedRamificationNumber v g hv : EReal`: `integerRamificationNumber` of `valuationIntegerAut v g hv`; it requires `v.valuationSubring` to be a discrete valuation ring.
- `normalizedAdditiveValue A x : EReal`, for a valuation subring `A` of `F` that is a discrete valuation ring: the normalized additive valuation of `x ∈ F` (uniformizers have value `1`), with value `⊤` at `0`. It is defined from Mathlib's valuation attached to the maximal ideal of `A`.

## Results

- `exists_addVal_eq_ramificationOrder`: the infimum of `addVal R (g a − a)` defining the ramification order is attained.
- The number is `⊤` exactly for `g = 1`, is at least `−1`, and has the form `n − 1` with `n ∈ ℕ` for `g ≠ 1`.
- `residueAut_eq_refl_iff`: `g` induces the identity on the residue field if and only if `g a − a` lies in the maximal ideal for all `a`. `integerRamificationNumber_eq_neg_one_of_residue_ne`: otherwise the number is `−1`.
- `integerRamificationNumber_eq_uniformizer`: if the residue field is perfect of characteristic `p` and `g` is trivial on it, then for every uniformizer `π` the number is `addVal R (g π − π) − 1`.
- The theorems `valuedRamificationNumber_*` state the same facts for `valuedRamificationNumber`.
- `normalizedAdditiveValue_coe`, `normalizedAdditiveValue_div`: the value extends `addVal` on `A`, and division by a nonzero element subtracts values.
- `ramificationOrder_eq_iInf_normalizedAdditiveValue`, `valuedRamificationNumber_eq_iInf`: `valuedRamificationNumber v g hv` is the infimum over integers `a` of the normalized value of `g a − a`, minus `1`.
- `valuedRamificationNumber_eq_uniformizer_ratio`: under the same hypotheses on the residue field, the number equals the normalized value of `g π / π − 1` for any uniformizer `π`.

## What to watch for

- These are the library's own notions. The number is the order minus one, so it is `−1` when `g` moves the residue field.
- The hypothesis `hv` that `g` preserves `v` is an explicit argument of the definitions.
- The uniformizer formulas need a perfect residue field of prime characteristic `p` and trivial action on it.

## References

Serre, *Local Fields*, Chapter IV; Wintenberger, *Le corps des normes de certaines extensions infinies de corps locaux; applications*, §1.1.1.

## Origin of the file

Copied from the Lean library FontaineWintenberger (https://github.com/YijunYuan/FontaineWintenberger), commit `e835d58871d8d564901c0f13b685034cd202659e`, file `FontaineWintenberger/Ramification/Embedding/Valued.lean` (SHA-256 of the source file `16d53460a2c121500a5945cb0a53de66c5ec66d7a34c51013b2cbbc25e79e1e2`). That library is distributed under the Apache License, Version 2.0; its licence text is kept with the Library's licences.

Changes made in the copy:

- The two Lean options that the library's lakefile sets and that differ from Lean's defaults are set after the imports (`relaxedAutoImplicit false`, `maxSynthPendingDepth 3`).
