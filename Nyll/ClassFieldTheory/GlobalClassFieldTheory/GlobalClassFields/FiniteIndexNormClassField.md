# A finite Galois norm neighbourhood inside a closed subgroup of finite index

Module `Nyll.ClassFieldTheory.GlobalClassFieldTheory.GlobalClassFields.FiniteIndexNormClassField`, copied unchanged from the Lean library NYLL. The origin of the file is given at the end of this page.

This file supplies the analytic input to the existence theorem of global class field theory. Let K be a number field and H a closed subgroup of finite index in the idèle class group C_K. The file constructs an explicit finite Galois extension M/K whose idèle-class norm group (the image of C_M in C_K under the norm) lies in H. M is the normal closure over K of a full S-unit Kummer extension of the cyclotomic field K(μ_n). The class field of H is later cut out of M by the finite abelian classification, but that step is not part of this file.

## Main definitions and results

- `closedFiniteIndexNormExponent H`: the Kummer exponent n, equal to the index [C_K : H] when H is proper and to 2 when H = C_K. `closedFiniteIndexNormExponent_eq_index` and `one_lt_closedFiniteIndexNormExponent` (always n > 1) record its properties.
- `closedFiniteIndexNormSeed H hclosed`: the finite seed of primes, namely the support of the finite part of the modulus `RayClass.modulusInsideClosedFiniteIndex H hclosed`, whose congruence subgroup lies in H.
- `closedFiniteIndexNormCyclotomicField`, `closedFiniteIndexNormKummerField` and `closedFiniteIndexNormAmbient`: the tower K ⊆ K(μ_n) ⊆ E ⊆ M. Here E is the cyclotomic full S-unit Kummer extension for n and the seed, and M is the finite normal closure of E over K. The file provides instances making each a number field, finite and Galois where appropriate. In particular M/K is finite Galois.
- `closedFiniteIndexSubgroup_has_finiteGaloisNormNeighborhood`: the norm group of M/K lies in H.

## Proof

The imported cyclotomic descent shows that the norm group of M/K lies in the power-local-unit subgroup C_K(S, ∅) for the enlarged support S. That subgroup consists of the classes of idèles that are n-th powers at infinite places and at S, and units at the other finite places. If H = C_K there is nothing more to prove. Otherwise n = [C_K : H] and S contains the seed. In that case `ideleClassPowerLocalUnitSubgroup_le_closedFiniteIndexSubgroup` gives C_K(S, ∅) ⊆ H, since n-th powers lie in a subgroup of index n and the units at the remaining places lie in the congruence subgroup.

## Points to watch

- Only the inclusion of the norm group in H is proved. The equality N = H for a suitable abelian subextension is obtained elsewhere.
- The case H = C_K is handled by the artificial choice n = 2, so that one construction covers all subgroups.

## Origin of the file

Copied unchanged from the Lean library NYLL (https://github.com/n-yamaguchi-0729/NYLL), commit `fe40c03df1b2b195053fdd63305571d97c73ce48`, file `Nyll/ClassFieldTheory/GlobalClassFieldTheory/GlobalClassFields/FiniteIndexNormClassField.lean`: the Lean file is the source byte for byte (SHA-256 `ba22990ee47694c815e38d4b061ef28e00197d210671e7e4c2e2046f66cc5ce3`). That library is distributed under the Apache License, Version 2.0; its licence and notice are kept with the Library's licences.
