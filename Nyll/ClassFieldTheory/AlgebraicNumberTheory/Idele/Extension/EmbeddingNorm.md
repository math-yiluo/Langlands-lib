# Norms as products over embeddings into a Galois extension

Module `Nyll.ClassFieldTheory.AlgebraicNumberTheory.Idele.Extension.EmbeddingNorm`, copied unchanged from the Lean library NYLL. The origin of the file is given at the end of this page.

Let `K ⊆ L ⊆ M` be fields with `L/K` finite and `M/K` finite Galois. The file proves that the determinant norm of `L` over `K`, after base change along any nontrivial commutative `K`-algebra `A` and extension of scalars to `M`, equals the product of the images under all `K`-embeddings `L → M`. Applied to `A = 𝔸_K`, this gives the norm formula for relative ideles:

`inclusion K M (norm K L a) = ∏ σ(a)`, the product over `Gal(M/K)/Gal(M/L)`.

## Main declarations

- `embeddingToAlgebraicClosureEquiv`: for `M/K` finite and normal, `K`-embeddings `L → M` correspond to `K`-embeddings `L → AlgebraicClosure M`.
- `fixingSubextension`, `restrictToSubextension`, `liftSubextensionEmbedding`, and `cosetEquivEmbedding`: the cosets of `Gal(M/L)` in `Gal(M/K)` correspond to the `K`-embeddings `L → M` (`M/K` normal).
- `norm_eq_prod_embeddings_in_galoisExtension`: the field norm of `x ∈ L` over `K` equals `∏_f f(x)` in `M`, over all `K`-embeddings `f : L → M`. It is deduced from Mathlib's `Algebra.norm_eq_prod_embeddings` in an algebraic closure, using separability of `L/K`.
- `embeddingPolynomial`, `embeddingProductPolynomial`, `map_normPolynomial_eq_embeddingProductPolynomial`: for a basis of `L/K`, the norm polynomial `normPolynomial b` (from the imported file on Galois norms), with coefficients extended to `M`, is the product of the linear forms of the embeddings. For `K` infinite this is checked by evaluation at points with coordinates in `K`.
- `scalarEmbedding A f`: the `A`-algebra map `id ⊗ f : A ⊗_K L → A ⊗_K M`.
- `includeLeft_norm_eq_prod_scalarEmbeddings` (`K` infinite, `A` nontrivial): the image in `A ⊗_K M` of the norm over `A` of `x ∈ A ⊗_K L` is the product of `scalarEmbedding A f x` over all `f`. `includeLeft_norm_eq_prod_galoisCosets` is the same product indexed by cosets. Both come from evaluating the polynomial identity at the coordinates of `x`.
- `adeleEmbedding f`, `ideleEmbedding f`: the induced maps on relative adeles and ideles, `𝔸_K ⊗_K L → 𝔸_K ⊗_K M`.
- `adeleInclusion_norm_eq_prod_embeddings`, `inclusion_norm_eq_prod_embeddings`, `inclusion_norm_eq_prod_galoisCosets`: the formula above for relative adeles and ideles, with `K` a number field.

## Points to watch

- The norms are the library's determinant norms on the tensor-product model `𝔸_K ⊗_K L` of the adeles of `L`.
- The general formula assumes `K` infinite; in the adelic section this follows from `K` being a number field.
- The coset index is Mathlib's quotient `(M ≃ₐ[K] M) ⧸ fixingSubextension`, whose classes are the cosets `σ·Gal(M/L)`, although the docstrings speak of right cosets.

## Origin of the file

Copied unchanged from the Lean library NYLL (https://github.com/n-yamaguchi-0729/NYLL), commit `fe40c03df1b2b195053fdd63305571d97c73ce48`, file `Nyll/ClassFieldTheory/AlgebraicNumberTheory/Idele/Extension/EmbeddingNorm.lean`: the Lean file is the source byte for byte (SHA-256 `c89dfd5bcf8364d0de026123875c9d08b4d5b186880e3b9df20dcac7ee873ad4`). That library is distributed under the Apache License, Version 2.0; its licence and notice are kept with the Library's licences.
