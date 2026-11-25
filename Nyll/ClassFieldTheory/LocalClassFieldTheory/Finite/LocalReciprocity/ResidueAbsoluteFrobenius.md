# Frobenius on an infinite Galois extension of a finite field

Module `Nyll.ClassFieldTheory.LocalClassFieldTheory.Finite.LocalReciprocity.ResidueAbsoluteFrobenius`, copied unchanged from the Lean library NYLL. The origin of the file is given at the end of this page.

Let `k` be a finite field and `Ω/k` an algebraic Galois extension, possibly infinite. The finite Frobenius maps `ZHat → Gal(E/k)` on finite Galois intermediate fields `E` are compatible with restriction, so they assemble, through the presentation of `Gal(Ω/k)` as an inverse limit, into a continuous homomorphism `ZHat → Gal(Ω/k)`.

- `finiteResidueFrobeniusIntermediate k Ω E`: the finite Frobenius map `ZHatMul →ₜ* Gal(E/k)` for a finite Galois intermediate field `E`.
- `residueFrobeniusToLimit`: these maps together, as a continuous homomorphism into the inverse limit of the finite Galois groups.
- `residueAbsoluteFrobenius k Ω : ZHatMul →ₜ* Gal(Ω/k)`: the composite with the inverse of the isomorphism from `Gal(Ω/k)` to that limit.
- `restrictNormalHom_residueAbsoluteFrobenius`: restricting `residueAbsoluteFrobenius z` to `E` gives the finite Frobenius coordinate of `z`.
- `restrictNormalHom_frobeniusAlgEquivOfAlgebraic` and `residueAbsoluteFrobenius_one`: arithmetic Frobenius on `Ω` restricts to arithmetic Frobenius on each `E`, and `1 ∈ ZHat` is sent to arithmetic Frobenius on `Ω`.

`ZHatMul` is `ZHat` written multiplicatively. The construction does not claim that the map is bijective; for an algebraic closure this is proved in another file.

## Origin of the file

Copied unchanged from the Lean library NYLL (https://github.com/n-yamaguchi-0729/NYLL), commit `fe40c03df1b2b195053fdd63305571d97c73ce48`, file `Nyll/ClassFieldTheory/LocalClassFieldTheory/Finite/LocalReciprocity/ResidueAbsoluteFrobenius.lean`: the Lean file is the source byte for byte (SHA-256 `04ee7acd3f8704b9a399a41f6b0943d5a10dee6e2aad427a365e89e641c2469b`). That library is distributed under the Apache License, Version 2.0; its licence and notice are kept with the Library's licences.
