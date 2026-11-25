# The norm quotient induced by a given local Artin map

Module `Nyll.ClassFieldTheory.Theorems.LocalClassFieldTheory.FiniteAbelianLocalReciprocityQuotientEquivOfArtin`, copied unchanged from the Lean library NYLL. The origin of the file is given at the end of this page.

Let K be a nonarchimedean local field (Mathlib's `IsNonarchimedeanLocalField`, with a valuative relation and a topology) and L/K a finite abelian extension.

`finiteAbelianLocalReciprocity_quotientEquiv_of_artin`: let `artin : Kˣ → Gal(L/K)` be a continuous surjective homomorphism whose kernel is the norm subgroup `fieldNormSubgroup K L`. Then there is exactly one isomorphism of topological groups `e` from the norm quotient `FieldNormQuotient K L` (Kˣ modulo the norms) onto Gal(L/K) with `e` of the class of `x` equal to `artin x` for every x in Kˣ.

The proof is the first isomorphism theorem. The kernel is open, as the preimage of the identity in the discrete Galois group, so the quotient is discrete and both directions of the isomorphism are continuous. Uniqueness holds because quotient classes are determined by representatives.

The map `artin` is a hypothesis: the theorem neither constructs the local Artin map nor shows that it is unique; as the file says, uniqueness of the quotient isomorphism is distinct from uniqueness of the Artin map.

## Origin of the file

Copied unchanged from the Lean library NYLL (https://github.com/n-yamaguchi-0729/NYLL), commit `fe40c03df1b2b195053fdd63305571d97c73ce48`, file `Nyll/ClassFieldTheory/Theorems/LocalClassFieldTheory/FiniteAbelianLocalReciprocityQuotientEquivOfArtin.lean`: the Lean file is the source byte for byte (SHA-256 `8cc4f91d054260d51c0e9a6984781bbdcc3e2293ba6a1a10f19a17aa410a4e17`). That library is distributed under the Apache License, Version 2.0; its licence and notice are kept with the Library's licences.
