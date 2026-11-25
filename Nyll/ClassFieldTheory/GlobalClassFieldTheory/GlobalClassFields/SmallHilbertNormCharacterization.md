# Norm groups of everywhere-unramified extensions

Module `Nyll.ClassFieldTheory.GlobalClassFieldTheory.GlobalClassFields.SmallHilbertNormCharacterization`, copied unchanged from the Lean library NYLL. The origin of the file is given at the end of this page.

Let L/K be a finite Galois extension of number fields. Assume it is unramified at all infinite places (`IsUnramifiedAtInfinitePlaces K L`) and that its set of ramified finite places, `ramifiedBaseFinitePlaces`, is empty. The file shows that every idele whose finite components are all local units is a norm from L. So the idele-class norm range of L/K contains the small-Hilbert norm subgroup. It draws the consequences for the class number.

## Main results

- `infiniteTensorNormSubgroup_eq_top_of_isUnramifiedAtInfinitePlaces`: at an infinite place unramified in L, the local norm image is the whole multiplicative group of the completion.
- `chosenFinitePlaceIsUnramified_of_no_ramifiedFinitePlaces`: with no ramified finite place, the chosen completion of L above each finite place v is unramified.
- `integralAtFinitePlaces_le_relativeIdeleNorm_range_of_everywhereUnramified`: the ideles whose finite components are all local units lie in the range of the relative idele norm.
- `smallHilbertClassFieldNormSubgroup_le_ideleClassNorm_range_of_everywhereUnramified`: the small-Hilbert norm subgroup lies in the range of the idele-class norm C_L → C_K.
- `smallHilbertClassFieldQuotientToIdeleClassNormQuotient`: the induced surjection between the quotients by these subgroups, with its kernel and the resulting isomorphism `smallHilbertNormImageQuotientEquivIdeleClassNormQuotient`.
- `classGroupToIdeleClassNormQuotient`: a surjection `ClassGroup (𝓞 K)` → C_K / N(C_L).
- `ideleClassNormQuotient_card_dvd_classNumber_of_everywhereUnramified`: the order of C_K / N(C_L) divides the class number. `classNumber_eq_unramifiedNormKernel_card_mul_normQuotient_card`: the class number is the order of the kernel of the previous map times that order.
- `cyclicEverywhereUnramifiedExtensionDegree_dvd_classNumber` and `classNumber_eq_unramifiedCyclicNormKernel_card_mul_extensionDegree`: if Gal(L/K) is moreover cyclic, then [L : K] divides the class number. The class number is then the order of the kernel times [L : K].

## Proof

An idele lies in the relative norm range when each local component is a local norm. This uses an imported criterion through local tensor norms. At infinite places the local degree is 1. At finite places the unramified local norm group contains the local units. The quotient and counting statements follow from the identification of the small-Hilbert quotient with the class group. The cyclic statements add the index formula `Reciprocity.ideleClassNorm_index_eq_finrank_abelian`, (C_K : N C_L) = [L : K] for abelian L/K.

## Points to watch

- "Everywhere unramified" includes the infinite places. Extensions ramified only at real places are excluded.
- The degree statements are stated for cyclic Gal(L/K), though the proof uses only the abelian index formula. For general Galois L/K the file gives only the divisibility of the norm index, not of the degree.
- Unramifiedness at finite places is checked through the library's chosen completions above each place.

## Origin of the file

Copied unchanged from the Lean library NYLL (https://github.com/n-yamaguchi-0729/NYLL), commit `fe40c03df1b2b195053fdd63305571d97c73ce48`, file `Nyll/ClassFieldTheory/GlobalClassFieldTheory/GlobalClassFields/SmallHilbertNormCharacterization.lean`: the Lean file is the source byte for byte (SHA-256 `41fd0e3c524d16b0e5e041e4e347353d711c94020514609a8e9df62f1dd387b7`). That library is distributed under the Apache License, Version 2.0; its licence and notice are kept with the Library's licences.
