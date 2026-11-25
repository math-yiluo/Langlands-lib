# The narrow finite conductor is computed place by place

Module `Nyll.ClassFieldTheory.GlobalClassFieldTheory.GlobalClassFields.ConductorLocalComparison`, copied unchanged from the Lean library NYLL. The origin of the file is given at the end of this page.

Let H be a subgroup of the idèle class group C_K of a number field K that admits a defining modulus. This file shows that the exponent of the narrow finite conductor of H at a finite prime v is a purely local invariant. It is the least n such that the image in C_K of the higher unit group U_v^(n) lies in H. Here U_v^(n) is placed at v, with 1 at every other place, as `RayClass.localHigherUnitClassSubgroup v n`. From this the file derives that some single defining modulus has the narrow finite conductor as its finite part.

## Main definitions and results

- `ConductorialSubgroup.narrowFiniteLocalConductorExponent H v`: the least n with `localHigherUnitClassSubgroup v n ≤ H`, with its specification and minimality. It is zero exactly when the image of the unit group O_vˣ lies in H (`narrowFiniteLocalConductorExponent_eq_zero_iff`).
- `replaceFiniteExponent_definingModulus`: in a defining modulus m, the exponent at v may be replaced by any n with U_v^(n) mapping into H. The real places of m are kept, and the result is again defining.
- `narrowFiniteConductorExponent_eq_narrowFiniteLocalConductorExponent` and `narrowFiniteConductor_apply_eq_narrowFiniteLocalConductorExponent`: the global minimum over defining moduli equals the local exponent at every v.
- `exists_definingModulus_finitePart_agrees_on_finset`: for any finite set s of primes there is a defining modulus whose finite part equals the conductor on s and the fixed bounding modulus off s.
- `exists_definingModulus_finitePart_eq_narrowFiniteConductor`: some defining modulus has finite part exactly the narrow finite conductor.
- `narrowFiniteConductor_antitone`: if H ≤ J, the conductor of J divides that of H.

## Proof

One inequality restricts a defining modulus to the place v. For the other, an idèle a in the congruence subgroup of the modified modulus is written as b · s. Here s carries the v-component of a at v, and b lies in the congruence subgroup of the original modulus. The existence of a defining modulus with finite part the conductor follows by induction over the support of one chosen defining modulus, replacing one exponent at a time.

## Points to watch

- The defining modulus with finite part equal to the conductor keeps the real places of the chosen modulus. Positivity is not removed here.

## Origin of the file

Copied unchanged from the Lean library NYLL (https://github.com/n-yamaguchi-0729/NYLL), commit `fe40c03df1b2b195053fdd63305571d97c73ce48`, file `Nyll/ClassFieldTheory/GlobalClassFieldTheory/GlobalClassFields/ConductorLocalComparison.lean`: the Lean file is the source byte for byte (SHA-256 `52d56cd9b9ddcecd6b867cf3a3d56b1625e9f14d44279a14b5de3d149535ff1b`). That library is distributed under the Apache License, Version 2.0; its licence and notice are kept with the Library's licences.
