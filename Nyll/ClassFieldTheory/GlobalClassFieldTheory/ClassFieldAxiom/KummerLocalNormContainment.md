# Local n-th powers are norms in extensions of exponent n

Module `Nyll.ClassFieldTheory.GlobalClassFieldTheory.ClassFieldAxiom.KummerLocalNormContainment`, copied unchanged from the Lean library NYLL. The origin of the file is given at the end of this page.

Let L/K be a finite abelian Galois extension of number fields whose Galois group has exponent dividing n. The file shows that at every finite place v of K, every n-th power in `K_vˣ` is a norm from the chosen localization of L at v (`chosenFinitePlaceLocalNormSubgroup`).

## Main results

- `galois_pow_eq_one_of_field_equiv_pi_zmod`: if `Gal(L/K) ≅ (ℤ/n)^r`, every automorphism satisfies `σⁿ = 1`.
- `nthPowerSubgroup_le_chosenFinitePlaceLocalNormSubgroup`: if `Gal(L/K) ≅ (ℤ/n)^r`, then `(K_vˣ)ⁿ` lies in the local norm subgroup at v.
- `chosenSimpleKummerNthPowerSubgroup_le_chosenFinitePlaceLocalNormSubgroup`: the same for the library's simple Kummer extension `K(ⁿ√b)`, when n is nonzero in K and K has a primitive n-th root of unity; the exponent bound comes from the Kummer character.

## Proof

A private lemma does the local work. The localization of L at the chosen place above v is an abelian Galois extension of the completion of K, whose group is identified with the decomposition group and so has exponent dividing n. After the completion is given the structure of a nonarchimedean local field, the norm subgroup is the kernel of the library's abelian local Artin map, and `yⁿ` maps to `Art(y)ⁿ = 1`. The result is transported to `v.adicCompletion K`.

## Points to watch

- The norm subgroup is the library's: norms from one chosen place above v, read in `v.adicCompletion K` through an identification of completions.
- The local step relies on the imported description of the local norm group as the kernel of the local Artin map.

## Origin of the file

Copied unchanged from the Lean library NYLL (https://github.com/n-yamaguchi-0729/NYLL), commit `fe40c03df1b2b195053fdd63305571d97c73ce48`, file `Nyll/ClassFieldTheory/GlobalClassFieldTheory/ClassFieldAxiom/KummerLocalNormContainment.lean`: the Lean file is the source byte for byte (SHA-256 `961dbdbbd746667a90a302ba5aab9fd5c24c1d280d12b0c4b4d240d9b8c8b95a`). That library is distributed under the Apache License, Version 2.0; its licence and notice are kept with the Library's licences.
