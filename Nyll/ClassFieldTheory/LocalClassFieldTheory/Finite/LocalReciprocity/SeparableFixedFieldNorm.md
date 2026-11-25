# Norms from finite separable intermediate fields

Module `Nyll.ClassFieldTheory.LocalClassFieldTheory.Finite.LocalReciprocity.SeparableFixedFieldNorm`, copied unchanged from the Lean library NYLL. The origin of the file is given at the end of this page.

Let `Ω/K` be a Galois extension with `Ω` separably closed, and `E` a finite separable intermediate field, not necessarily normal over `K`. The Henselian condition of the abstract class formation quantifies over all finite abstract fields, normal or not. This file shows that the class-formation norm from `E` to `K`, a product over the left cosets of `Gal(Ω/E)` in `Gal(Ω/K)`, is the ordinary field norm.

## Main definitions and results

- `baseFixingCosetToAlgHom`: sends the coset of `σ` to the `K`-embedding `σ|E : E → Ω`; it is injective (`baseFixingCosetToAlgHom_injective`) and, for `E` finite separable, surjective (`baseFixingCosetToAlgHom_surjective`).
- `baseFixingCosetEquivAlgHom`: the resulting bijection between these cosets and the `K`-embeddings of `E` into `Ω`; the instance `baseFixingExtensionQuotient_finite_of_isSeparable` deduces that there are finitely many cosets.
- `relativeCosetAction_intermediateFieldUnit_val_of_isSeparable`: the coset action on a unit of `E` is evaluation of the corresponding embedding.
- `relativeNorm_intermediateFieldUnit_val_of_isSeparable`: for `x ∈ Eˣ`, the class-formation norm of `x`, as an element of `Ω`, equals the image of the field norm of `x` from `E` to `K`.
- `relativeNorm_intermediateFieldUnit_of_isSeparable`: the same as an equality of fixed units, the right side being the image of `normUnits K E x`.

Both norms are written as the product of `σ(x)` over all embeddings `σ : E → Ω`, by reindexing along the bijection and by the formula for the norm into a separably closed field.

## Points to watch

The ambient field must be separably closed, and `E/K` finite and separable, for surjectivity and the norm identity. The statements about the class-formation coset action and norm take `K` and `Ω` in `Type`; the coset bijection with embeddings is universe-polymorphic.

## Origin of the file

Copied unchanged from the Lean library NYLL (https://github.com/n-yamaguchi-0729/NYLL), commit `fe40c03df1b2b195053fdd63305571d97c73ce48`, file `Nyll/ClassFieldTheory/LocalClassFieldTheory/Finite/LocalReciprocity/SeparableFixedFieldNorm.lean`: the Lean file is the source byte for byte (SHA-256 `1d4eb93ff88319e56a90cdd6a83e93ecc5756f45a55c6353f6587c25df201e17`). That library is distributed under the Apache License, Version 2.0; its licence and notice are kept with the Library's licences.
