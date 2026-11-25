# The Frobenius semigroup

Module `Nyll.ClassFieldTheory.AbstractClassFieldTheory.Reciprocity.Construction.FrobeniusSemigroup`, copied unchanged from the Lean library NYLL. The origin of the file is given at the end of this page.

In the abstract construction of the reciprocity map, the Frobenius elements `Frob(L̃ | K)` of `G_K / I_L` are the classes whose normalized degree is a positive natural number. This file shows that they are closed under multiplication, the degrees adding. Here `K` is a finite residue abstract field for the degree map `D`, and `L ≤ K` is a closed subgroup with `G_L` normal in `G_K`.

- `DegreeData.frobeniusMul`: the product `σ τ` of two Frobenius elements, again a Frobenius element, with exponent `m + n` where `m` and `n` are the exponents of `σ` and `τ`.
- `frobeniusElementsMul` and `frobeniusElementsSemigroup`: the resulting `Mul` and `Semigroup` instances on `D.FrobeniusElements K L hLK`; `frobeniusMul_coe` says the product is computed in `G_K / I_L`.
- `extensionNormalizedDegree_frobenius_mul`: the normalized degree is multiplicative on products of Frobenius elements, in the multiplicative notation for `Ẑ`.

Only a semigroup structure is defined: degree `0` is excluded, so the identity class is not a Frobenius element.

## Origin of the file

Copied unchanged from the Lean library NYLL (https://github.com/n-yamaguchi-0729/NYLL), commit `fe40c03df1b2b195053fdd63305571d97c73ce48`, file `Nyll/ClassFieldTheory/AbstractClassFieldTheory/Reciprocity/Construction/FrobeniusSemigroup.lean`: the Lean file is the source byte for byte (SHA-256 `d6f0e9ec216bbacb8043fe074a6fc22fd8ffd494e4b3666436fc58a4a0aef514`). That library is distributed under the Apache License, Version 2.0; its licence and notice are kept with the Library's licences.
