# Unramified places and the exponents of abelian norm conductors

Module `Nyll.ClassFieldTheory.GlobalClassFieldTheory.GlobalClassFields.AbelianNormConductor`, copied unchanged from the Lean library NYLL. The origin of the file is given at the end of this page.

Let `L / K` be a finite abelian extension of number fields and `v` a finite place of `K`. The file shows that the local higher-unit exponent at `v` of the idele-class norm subgroup, `ideleClassNormLocalHigherUnitExponent v`, vanishes exactly when the chosen completed extension at `v` is unramified.

## Main results

- `ideleClassNormLocalHigherUnitExponent_eq_zero_iff_chosenFinitePlaceIsUnramified`: `ideleClassNormLocalHigherUnitExponent v = 0` iff `ChosenFinitePlaceIsUnramified v`.
- `mem_ideleClassNormDefiningModulus_support_iff_not_chosenFinitePlaceIsUnramified`: hence `v` lies in the support of the norm-defining modulus iff the chosen completed extension at `v` is ramified.

## Proof

The implication from unramified to exponent zero is imported. For the converse, exponent zero means every integral unit of the adic completion `K_v` lies in the chosen local norm subgroup. Transporting these units to the absolute-value completion used by local class field theory shows that all units are norms from the localized completion `E`. So the local conductor exponent of `E` is `0`, and the local criterion (conductor exponent zero iff unramified) concludes.

## Points to watch

- Unramifiedness is that of the localized completion at one chosen place of `L` above `v`.
- The converse direction rests on local class field theory through the imported local conductor-zero criterion.

## Origin of the file

Copied unchanged from the Lean library NYLL (https://github.com/n-yamaguchi-0729/NYLL), commit `fe40c03df1b2b195053fdd63305571d97c73ce48`, file `Nyll/ClassFieldTheory/GlobalClassFieldTheory/GlobalClassFields/AbelianNormConductor.lean`: the Lean file is the source byte for byte (SHA-256 `8b81f8fc5c0671c34b39653bfe716d330259910b345e8c611d83bd1a1f9d0963`). That library is distributed under the Apache License, Version 2.0; its licence and notice are kept with the Library's licences.
