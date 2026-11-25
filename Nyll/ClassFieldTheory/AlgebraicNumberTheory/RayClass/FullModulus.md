# Ray moduli and idelic ray class groups

Module `Nyll.ClassFieldTheory.AlgebraicNumberTheory.RayClass.FullModulus`, copied unchanged from the Lean library NYLL. The origin of the file is given at the end of this page.

For a number field `K`, a modulus is a finite modulus together with a finite set of real places at which positivity is imposed. This file defines moduli, their order, the congruence subgroups of the ideles and of the idele class group, and the ray class group as a quotient of the idele class group.

## Main definitions and results

- `RayClass.RealPlace K`: the real infinite places. `RayClass.Modulus K`: a structure with `finitePart`, a finite modulus (exponents at finite places), and `infinitePart`, a finite set of real places.
- `Modulus.ofFinite m` (no real places), `Modulus.narrowOfFinite m` (all real places), `0`; extensionality; the componentwise order (pointwise `≤` on exponents, inclusion of real places), with infima, suprema and a least element.
- `replaceFinitePart`, `eraseRealPlace`, `eraseRealPlaces`: change the finite part, or remove real places, with simp lemmas.
- `Modulus.localInfiniteCongruenceSubgroup m w`: the positive elements of `K_wˣ` if `w` is a real place selected by `m`, the whole group otherwise. `Modulus.infiniteCongruenceSubgroup m`: infinite ideles in these local subgroups; for `narrowOfFinite` it is the subgroup positive at every real place.
- `Modulus.ideleCongruenceSubgroup m`: the product of the infinite congruence subgroup and `finiteCongruenceSubgroup` of the finite part, so local units at finite places outside the support, `U_v^(n)` at places of the support with exponent `n`, positive at the selected real places. The narrow case is computed by `ideleCongruenceSubgroup_narrowOfFinite`.
- `Modulus.congruenceSubgroup m`: the image of `ideleCongruenceSubgroup m ⊔ Kˣ` in the idele class group; it is normal, the idele class group being commutative.
- `RayClass.RayClassGroup m`: the idele class group modulo the congruence subgroup. `rayClassGroupEquivIdeleQuotient` identifies it with `I_K / (ideleCongruenceSubgroup m ⊔ Kˣ)`.

## Points to watch

- The ray class group is defined idelically. Its identification with the classical group of fractional ideals prime to the modulus, modulo the ray, is not in this file; neither is its finiteness.
- The order on moduli compares exponents pointwise, which is divisibility of moduli.

## Origin of the file

Copied unchanged from the Lean library NYLL (https://github.com/n-yamaguchi-0729/NYLL), commit `fe40c03df1b2b195053fdd63305571d97c73ce48`, file `Nyll/ClassFieldTheory/AlgebraicNumberTheory/RayClass/FullModulus.lean`: the Lean file is the source byte for byte (SHA-256 `f75bf49da5908248e7a735d7bb401e926635b317cfb2c3c5e7ab046a5274ecb0`). That library is distributed under the Apache License, Version 2.0; its licence and notice are kept with the Library's licences.
