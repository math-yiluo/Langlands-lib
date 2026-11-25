# Norm group of the full S-unit Kummer extension

Module `Nyll.ClassFieldTheory.GlobalClassFieldTheory.GlobalClassFields.SUnitKummerNormRealization`, copied unchanged from the Lean library NYLL. The origin of the file is given at the end of this page.

Let K be a number field containing a primitive n-th root of unity, n > 1. For a finite set `seed` of finite places, let S be the library's canonical support `sUnitKummerNormSupport n seed`. Let E ⊆ Ω be the full S-unit Kummer extension of exponent n inside a separable closure Ω of K.

## Main result

`fullSUnitKummerExtension_ideleClassNormRange_eq_powerLocalUnit`: the range of the idele-class norm C_E → C_K equals `ideleClassPowerLocalUnitSubgroup n S ∅`.

## Proof

E/K is abelian with group (ℤ/n)^r, unramified at finite places outside S, and n is even or K has no real place. The local norm theorem then puts the power-local-unit subgroup inside the norm range. Both subgroups have index [E : K]. For the power subgroup, a quotient count done elsewhere gives this. For the norm range, the global index formula `Reciprocity.ideleClassNorm_index_eq_finrank_abelian` does. Inclusion with equal finite index gives equality.

## Points to watch

S must be the canonical support, not an arbitrary finite set of places.

## Origin of the file

Copied unchanged from the Lean library NYLL (https://github.com/n-yamaguchi-0729/NYLL), commit `fe40c03df1b2b195053fdd63305571d97c73ce48`, file `Nyll/ClassFieldTheory/GlobalClassFieldTheory/GlobalClassFields/SUnitKummerNormRealization.lean`: the Lean file is the source byte for byte (SHA-256 `63c30de3d853c0ce023cfd0a4acfecdf6e446f3046148b785496f41d94d1a25a`). That library is distributed under the Apache License, Version 2.0; its licence and notice are kept with the Library's licences.
