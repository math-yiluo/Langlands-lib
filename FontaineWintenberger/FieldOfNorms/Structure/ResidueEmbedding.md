# The embedding of the residue field of L in the field of norms

Module `FontaineWintenberger.FieldOfNorms.Structure.ResidueEmbedding`, copied from the Lean library FontaineWintenberger. The origin of the file and the changes made in the copy are given at the end of this page.

Let `L/K` be an APF extension of a field `K` with `IsPerfectResidueLocalField K`, `p` the residue characteristic, `κL` the residue field of the integral closure of `𝒪[K]` in `L`, and `K₀ ⊆ K₁` the maximal unramified and maximal tame subextensions (`apfMaximalUnramified`, `apfMaximalTame`). The file builds a field embedding `κL → FieldOfNorms K L` from Teichmüller representatives of `p`-power roots, and shows that it induces an isomorphism of `κL` with the residue field of the field of norms.

## Extension from a cofinal tail (any fields `K ⊆ L`)

- `FiniteIntermediateField.norm_inclusion`: the norm from `F` to `E` of `x ∈ E` is `x ^ [F : E]`.
- `existsUnique_fieldOfNorms_of_compatible_tail`, `FieldOfNorms.ofTail`: a norm-compatible family given on the finite `E ⊇ D` extends uniquely to an element of the field of norms.

## The constants

- `residueDegree E hE`: for finite `E ⊇ K₁`, the exponent `d` with `[E : K₁] = p^d`; these exponents add in towers (`residueDegree_step`).
- `residueRoot E hE : κL ≃+* (residue field of K₀)`: the identification of the residue fields followed by the inverse of the `d`-fold Frobenius.
- `residueIntegralCoordinate`, `residueCoordinate`: the Teichmüller lift in `K₀` of `residueRoot E hE x`, viewed in `E`. It is the Teichmüller lift in `E` of `residueCoordinateEquiv E hE x`, where `residueCoordinateEquiv : κL ≃+* (residue field of E)`.
- `residueCoordinate_norm`: these coordinates are norm-compatible.
- `residueConstants : κL →*₀ FieldOfNorms K L`: the resulting multiplicative map; it is injective and takes integral values.

Assuming also that `L/K` is infinite:

- `deepResidueEquiv`: the residue field of the stage `𝔈 n` of `deepFiniteTower K L K₁` is that of its truncated quotient, which is therefore perfect of characteristic `p`.
- `residueTruncatedHom`, `FieldOfNorms.truncation_residueConstantsInteger`: each truncation of a constant is given by a ring homomorphism `κL → DeepFiniteTowerQuotient K L K₁ n`.
- `residueConstantsInteger_add`, `residueConstantsIntegerHom`, `residueConstantsFieldEmbedding`: the constants are additive, so they form a ring homomorphism into the valuation ring and an injective field homomorphism into the field of norms.
- `FieldOfNorms.residueEquiv : κL ≃+* (residue field of the field of norms)` (called Theorem 2.1.3 (ii) in the file); it sends `x` to the residue of its constant (`residueEquiv_apply`).

## Proofs

Additivity is checked on every truncation, by naturality of the Teichmüller section and injectivity of `FieldOfNorms.truncationEquiv`.

## Points to watch

- `residueDegree` is an exponent of a field degree over `K₁`, not a residue degree.
- The coordinate at `E` uses a `p^d`-th root: the embedding is twisted by inverse Frobenius at each stage.

## References

Wintenberger, *Le corps des normes de certaines extensions infinies de corps locaux; applications*, §2–3.

## Origin of the file

Copied from the Lean library FontaineWintenberger (https://github.com/YijunYuan/FontaineWintenberger), commit `e835d58871d8d564901c0f13b685034cd202659e`, file `FontaineWintenberger/FieldOfNorms/Structure/ResidueEmbedding.lean` (SHA-256 of the source file `debc3ba504209f1e98c8151fa177e6d15f7d9f47e8588c5ddc7e9d7693ddd512`). That library is distributed under the Apache License, Version 2.0; its licence text is kept with the Library's licences.

Changes made in the copy:

- The two Lean options that the library's lakefile sets and that differ from Lean's defaults are set after the imports (`relaxedAutoImplicit false`, `maxSynthPendingDepth 3`).
