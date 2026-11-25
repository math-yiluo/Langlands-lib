# Embeddings into a separable closure

Module `Nyll.ClassFieldTheory.AlgebraicNumberTheory.SeparableClosureEmbedding`, copied unchanged from the Lean library NYLL. The origin of the file is given at the end of this page.

The file fixes a copy of a separable extension inside Mathlib's separable closure of the base field, and shows that conjugation by a field isomorphism is continuous for the Krull topologies.

- `continuous_algEquiv_autCongr`: for an `F`-algebra isomorphism of fields `e : E ≃ₐ[F] E'`, the induced isomorphism `σ ↦ e ∘ σ ∘ e⁻¹` from `Aut_F(E)` to `Aut_F(E')` is continuous for the Krull topologies. It is checked at the identity: the fixing subgroup of a finite-dimensional `M ⊆ E'` contains the image of the fixing subgroup of `e⁻¹(M)`.
- `separableEmbeddingIntoSeparableClosure K L`: for a separable extension `L/K`, a chosen `K`-embedding `L →ₐ[K] SeparableClosure K`.
- `numberFieldSeparableClosureEmbedding K`: for a number field `K`, a chosen `ℚ`-embedding into `SeparableClosure ℚ`.
- `numberFieldInRationalSeparableClosure K`: the image of that embedding, an intermediate field of `SeparableClosure ℚ`, with instances saying it is finite-dimensional over `ℚ` and a number field.

## Points to watch

The embeddings are arbitrary choices made by `IsSepClosed.lift`; nothing in the file relates the choices made for different fields.

## Origin of the file

Copied unchanged from the Lean library NYLL (https://github.com/n-yamaguchi-0729/NYLL), commit `fe40c03df1b2b195053fdd63305571d97c73ce48`, file `Nyll/ClassFieldTheory/AlgebraicNumberTheory/SeparableClosureEmbedding.lean`: the Lean file is the source byte for byte (SHA-256 `2e104075b1bbd4c70ec298e03433b5f10c2c779caeaa373af1acf54e23e88bd9`). That library is distributed under the Apache License, Version 2.0; its licence and notice are kept with the Library's licences.
