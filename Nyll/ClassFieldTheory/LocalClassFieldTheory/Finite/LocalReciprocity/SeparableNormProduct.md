# Separable field norms as products over embeddings

Module `Nyll.ClassFieldTheory.LocalClassFieldTheory.Finite.LocalReciprocity.SeparableNormProduct`, copied unchanged from the Lean library NYLL. The origin of the file is given at the end of this page.

For a finite separable extension `E/k` and a separably closed field `Ω` containing `k`, the image in `Ω` of the norm of `x ∈ E` over `k` is the product of `σ(x)` over all `k`-embeddings `σ : E → Ω`. `Ω` need not be normal over `k`.

- `algebraMap_norm_eq_prod_embeddings_of_isSepClosed`: the formula above, for every `x ∈ E`.
- `prod_embeddings_algebraMap_powerBasisGen_eq`: for a tower `k ⊂ L ⊂ E` of finite separable extensions and a power basis of `L/k` with generator `g`, the product of `σ(g)` over embeddings of `E` is the product over embeddings of `L` raised to the power `[E : L]`.

The proof reduces to the field `k(x)`, where the norm is the product over embeddings of a power-basis generator, and uses that every embedding of `k(x)` extends to `E` in exactly `[E : k(x)]` ways because `Ω` is separably closed.

## Origin of the file

Copied unchanged from the Lean library NYLL (https://github.com/n-yamaguchi-0729/NYLL), commit `fe40c03df1b2b195053fdd63305571d97c73ce48`, file `Nyll/ClassFieldTheory/LocalClassFieldTheory/Finite/LocalReciprocity/SeparableNormProduct.lean`: the Lean file is the source byte for byte (SHA-256 `336acc33acdd5b782461de62e08458810d284bba72983b7c497f2caaab09ca54`). That library is distributed under the Apache License, Version 2.0; its licence and notice are kept with the Library's licences.
