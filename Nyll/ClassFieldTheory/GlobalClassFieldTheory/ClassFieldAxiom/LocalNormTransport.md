# Transport of norm conditions along field isomorphisms

Module `Nyll.ClassFieldTheory.GlobalClassFieldTheory.ClassFieldAxiom.LocalNormTransport`, copied unchanged from the Lean library NYLL. The origin of the file is given at the end of this page.

Let `eK : K ≃ₐ[ℚ] K'` be an isomorphism of number fields and `eL : L ≃+* L'` a ring isomorphism compatible with the algebra maps, with L/K and L'/K' finite. The file shows that the library's norm predicates are preserved when x ∈ Kˣ is replaced by `eK x` and places are matched through `eK`.

- `isNormAtFinitePlace_congr`, `isNormAtInfinitePlace_congr`: x is a local norm at the place corresponding to W exactly when `eK x` is a local norm at W.
- `isEverywhereLocalNorm_congr`: x is a norm at every place exactly when `eK x` is.
- `isFieldNorm_congr`: x is a norm from Lˣ exactly when `eK x` is a norm from L'ˣ; here `eK` need only be a ring isomorphism and K, K' need not be number fields.

The local statements use an imported compatibility of tensor determinant norms with the induced isomorphisms of completions.

## Points to watch

- `IsNormAtFinitePlace` and `IsNormAtInfinitePlace` are the library's predicates, defined through the determinant norm of `K_v ⊗[K] L`.

## Origin of the file

Copied unchanged from the Lean library NYLL (https://github.com/n-yamaguchi-0729/NYLL), commit `fe40c03df1b2b195053fdd63305571d97c73ce48`, file `Nyll/ClassFieldTheory/GlobalClassFieldTheory/ClassFieldAxiom/LocalNormTransport.lean`: the Lean file is the source byte for byte (SHA-256 `d7365164e865dc956d7459d2524e67c692c6ced30ae5a03dace96293a628cfaa`). That library is distributed under the Apache License, Version 2.0; its licence and notice are kept with the Library's licences.
