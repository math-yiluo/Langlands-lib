# The class-formation norm on units of a Galois extension

Module `Nyll.ClassFieldTheory.LocalClassFieldTheory.Finite.LocalReciprocity.SeparableUnitsNorm`, copied unchanged from the Lean library NYLL. The origin of the file is given at the end of this page.

In local class field theory the coefficient module is the unit group of a separable closure. For a Galois extension `Ω/K`, possibly infinite, and a finite Galois intermediate field `E`, this file compares the norm of the abstract class formation, a sum over cosets of `Gal(Ω/E)` in `Gal(Ω/K)`, with the field norm from `E` to `K`, and identifies the abstract norm quotient with `Kˣ / N(Eˣ)`. Working with an arbitrary Galois `Ω` avoids assuming `K` perfect.

## Main definitions and results

- `baseUnitsEquivGaloisAmbientFixed`: `Kˣ` is isomorphic to the units of `Ω` fixed by the base subgroup, by the algebra map (`baseUnitsEquivGaloisAmbientFixed_val`).
- `baseFixingExtensionQuotient_finite` (instance): the quotient for a finite Galois `E` is finite.
- `relativeCosetAction_intermediateFieldUnit_val`: the coset action on a unit of `E` is the action of the corresponding element of `Gal(E/K)`.
- `relativeNorm_intermediateFieldUnit_val` and `relativeNorm_intermediateFieldUnit`: for `x ∈ Eˣ`, the abstract relative norm of `x` is the image of the field norm of `x` from `E` to `K`.
- `map_finiteNormSubgroup_eq_additiveNormSubgroup`: under the identification of `Kˣ` with fixed units, the abstract norm subgroup is the field norm subgroup.
- `finiteNormQuotientEquivNormQuotient`: the abstract finite norm quotient is isomorphic to `NormQuotient K E` (written additively); `finiteNormQuotientEquivNormQuotient_finiteNormClass` says it sends the class of `a` to the norm class of the corresponding element of `Kˣ`.
- For a finite Galois `L` with an embedding `i : L →ₐ[K] Ω`: `normUnits_embeddedExtensionAlgEquiv` and `localNormSubgroup_fieldRange_eq` (the norm subgroup does not depend on the realization), `relativeNorm_embeddedExtensionUnit`, and `finiteNormQuotientEquivEmbeddedNormQuotient` with its value on norm classes, identifying the abstract quotient for the image of `L` with `NormQuotient K L`.

## Proofs

The coset sum is reindexed along the isomorphism of the coset space with `Gal(E/K)`, and the field norm of a Galois extension is the product of the conjugates. The quotient isomorphism combines the subgroup comparison with the first isomorphism theorem.

## Points to watch

The intermediate field must be Galois over `K` here; the norm comparison for non-normal finite separable fields, which needs `Ω` separably closed, is in a separate file.

## Origin of the file

Copied unchanged from the Lean library NYLL (https://github.com/n-yamaguchi-0729/NYLL), commit `fe40c03df1b2b195053fdd63305571d97c73ce48`, file `Nyll/ClassFieldTheory/LocalClassFieldTheory/Finite/LocalReciprocity/SeparableUnitsNorm.lean`: the Lean file is the source byte for byte (SHA-256 `d473706109aade4763921b83453becac045267e32fce1b0bf89b32f1a14cc730`). That library is distributed under the Apache License, Version 2.0; its licence and notice are kept with the Library's licences.
