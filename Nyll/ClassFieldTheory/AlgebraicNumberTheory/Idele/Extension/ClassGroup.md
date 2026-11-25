# Idele classes in a finite extension: inclusion and norm

Module `Nyll.ClassFieldTheory.AlgebraicNumberTheory.Idele.Extension.ClassGroup`, copied unchanged from the Lean library NYLL. The origin of the file is given at the end of this page.

For a finite extension `L/K` of number fields, with the ideles of `L` modelled as the units of `𝔸_K ⊗_K L`, the file defines the relative idele class group, maps `C_K` into it, and proves that this map is injective. It also passes the relative idele norm to idele classes. The key point is `I_K ∩ Lˣ = Kˣ` inside the relative ideles.

## Main declarations

- `exists_scalar_of_adeleInclusion_eq_fieldInclusion`: if `a ⊗ 1 = 1 ⊗ x` with `a ∈ 𝔸_K` and `x ∈ L`, then both come from one scalar `k ∈ K`. The proof applies `ε ⊗ id`, where `ε` is a `K`-linear left inverse of `K → 𝔸_K`.
- `principalSubgroup`: the image of `Lˣ` in the relative ideles. `ClassGroup K L` is the quotient by it.
- `comap_principalSubgroup`: the preimage of the principal relative ideles under `inclusion : I_K → I_L` is the group of principal ideles of `K`.
- `classInclusion : IdeleClassGroup K →* ClassGroup K L`, the map induced on quotients, and `classInclusion_injective`: it is injective, from the previous result.
- `classNorm : ClassGroup K L →* IdeleClassGroup K`, induced by the determinant norm `RelativeIdeleGroup.norm`, which sends principal ideles to principal ideles.
- `ClassNormQuotient`: the quotient `C_K / N(C_L)`, the image of `classNorm`; here it is only defined.

## Points to watch

- `ClassGroup K L` is the library's tensor-product model of `C_L`, not a quotient of Mathlib's ideles of `L`.
- No Galois hypothesis is made. The intersection statement and the injectivity also drop finiteness of `L/K` and the number-field hypothesis on `L`; `classNorm` uses finite dimensionality.

## Origin of the file

Copied unchanged from the Lean library NYLL (https://github.com/n-yamaguchi-0729/NYLL), commit `fe40c03df1b2b195053fdd63305571d97c73ce48`, file `Nyll/ClassFieldTheory/AlgebraicNumberTheory/Idele/Extension/ClassGroup.lean`: the Lean file is the source byte for byte (SHA-256 `5ef38e61f6579fddd7b40b7e63850ee938422690ee329e544553c57dac84ac0a`). That library is distributed under the Apache License, Version 2.0; its licence and notice are kept with the Library's licences.
