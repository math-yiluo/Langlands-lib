# Cyclotomic descent of S-unit Kummer norm subgroups

Module `Nyll.ClassFieldTheory.GlobalClassFieldTheory.GlobalClassFields.CyclotomicKummerNormDescent`, copied unchanged from the Lean library NYLL. The origin of the file is given at the end of this page.

This file carries out the roots-of-unity descent step of the existence theorem of global class field theory. Let K be a number field and n > 1. Over the cyclotomic field C = K(μ_n), Kummer theory gives a finite abelian extension E whose idèle-class norm group is known explicitly. Here E is the full S-unit Kummer extension, obtained by adjoining n-th roots of S-units. The norm group is the power-local-unit subgroup C_C(S′, ∅): the classes of idèles that are n-th powers at the infinite places and at the places of S′, and units at the other finite places. The file chooses the support so that this description descends to K. It then passes to the Galois closure of E over K.

## Main definitions and results

- `cyclotomicKummerNormSupport n seed`: a finite set S of finite places of K. It contains the given `seed` and the places below the Kummer support that `sUnitKummerNormSupport` attaches to the places of C above the seed. That support includes the places in `IdeleGroup.sufficientlyLargeFiniteSet` and those dividing n.
- `cyclotomicKummerNormSupportAbove n seed`: S′, all places of C lying over places of S. `mem_cyclotomicKummerNormSupportAbove_iff` says that W ∈ S′ exactly when the place below W is in S.
- `sUnitKummerNormSupport_cyclotomicKummerNormSupportAbove`: S′ is already stable under the Kummer enlargement over C. As a consequence `cyclotomicKummerNormSupport_idem` says that the enlargement of S is idempotent.
- `cyclotomicFullSUnitKummerExtension n seed`: the full S′-unit Kummer extension E of C inside a separable closure of C. It is Galois and finite over C and a number field (`cyclotomicKummerNormDescent_kummerNumberField`, deliberately not an instance).
- `cyclotomicFullSUnitKummerExtension_ideleClassNormRange_le_powerLocalUnit`: for n > 1, with E viewed over K, the norm group of E over K lies in `ideleClassPowerLocalUnitSubgroup n S ∅` over K.
- `cyclotomicFullSUnitKummerFiniteNormalClosure_ideleClassNormRange_le_powerLocalUnit`: the same inclusion for the finite normal closure F of E over K, which is a finite Galois extension of K.

## Proof

Over C, the imported Kummer norm theorem `fullSUnitKummerExtension_ideleClassNormRange_eq_powerLocalUnit` identifies the norm group of E over C with C_C(S′, ∅); stability of S′ removes the enlargement. Transitivity of the norm in K ⊆ C ⊆ E sends this group into C_K(S, ∅). This uses that S′ is the full inverse image of S (`ideleClassNorm_map_powerLocalUnitSubgroup_le_of_supports_above`). Passing to the normal closure can only shrink the norm group (`finiteNormalClosure_ideleClassNorm_range_le_source`).

## Points to watch

- Over K only an inclusion of norm groups is proved, not an equality; equality holds over the cyclotomic field C.
- The main results need n > 1 (hypothesis `hn`). The support S depends on choices made by the library (the sufficiently large set and the unit support of n).

## Origin of the file

Copied unchanged from the Lean library NYLL (https://github.com/n-yamaguchi-0729/NYLL), commit `fe40c03df1b2b195053fdd63305571d97c73ce48`, file `Nyll/ClassFieldTheory/GlobalClassFieldTheory/GlobalClassFields/CyclotomicKummerNormDescent.lean`: the Lean file is the source byte for byte (SHA-256 `9930b06d5095d199dc0860232221fa5aad0304e8434b8cea02b9452cc022f48b`). That library is distributed under the Apache License, Version 2.0; its licence and notice are kept with the Library's licences.
