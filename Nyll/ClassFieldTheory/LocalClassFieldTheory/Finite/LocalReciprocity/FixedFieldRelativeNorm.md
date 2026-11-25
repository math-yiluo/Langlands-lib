# Relative norms on fixed fields as field norms

Module `Nyll.ClassFieldTheory.LocalClassFieldTheory.Finite.LocalReciprocity.FixedFieldRelativeNorm`, copied unchanged from the Lean library NYLL. The origin of the file is given at the end of this page.

Let `Ω/k` be a Galois extension with `Ω` separably closed, and let `L ≤ K` be closed subgroups of `Gal(Ω/k)`. The class formation on the units of `Ω` has a relative norm from `L`-fixed to `K`-fixed units, defined as a product over the left cosets of `L` in `K`. This file shows that it is the ordinary field norm from the fixed field of `L` to the fixed field of `K`, without assuming that this extension is normal.

## Main definitions and results

- `abstractFixedFieldCosetToAlgHom`: sends the coset of `σ ∈ K` to the embedding of the fixed field of `L` into `Ω`, over the fixed field of `K`, given by restricting `σ`.
- `abstractFixedFieldCosetToAlgHom_injective` and `abstractFixedFieldCosetToAlgHom_surjective`: this map is injective, and surjective when the fixed field of `L` is finite-dimensional over that of `K` (surjectivity uses that `Ω` is separably closed). `abstractFixedFieldCosetEquivAlgHom` is the resulting bijection between `K/L` and these embeddings.
- `relativeCosetAction_abstractFixedFieldUnit_val`: the coset action on a fixed unit is evaluation of the corresponding embedding.
- `relativeNorm_abstractFixedFieldUnit_eq_normUnits`: when `K/L` is finite and `K` has finite index in `Gal(Ω/k)`, the relative norm of a unit `x` of the fixed field of `L`, read as a fixed unit of `Ω`, equals the image of `normUnits x`, the field norm of `x`.

## Proof

Both norms are the product of the conjugates of `x` under all embeddings into `Ω`: the coset product is reindexed by the bijection above, and the field norm is compared with the product over embeddings into a separably closed field. Finite-dimensionality comes from the two finiteness hypotheses.

## Points to watch

- The ambient field `Ω` must be separably closed (in addition to Galois over `k`) for surjectivity and the norm identity.
- Finiteness of `K/L` and of the index of `K` are instance arguments.
- The fields `k` and `Ω` are taken in `Type`.

## Origin of the file

Copied unchanged from the Lean library NYLL (https://github.com/n-yamaguchi-0729/NYLL), commit `fe40c03df1b2b195053fdd63305571d97c73ce48`, file `Nyll/ClassFieldTheory/LocalClassFieldTheory/Finite/LocalReciprocity/FixedFieldRelativeNorm.lean`: the Lean file is the source byte for byte (SHA-256 `7869ec1f615acda445c68f8d4eff291cc77b8ac3a33bd531510e5b66f9da1171`). That library is distributed under the Apache License, Version 2.0; its licence and notice are kept with the Library's licences.
