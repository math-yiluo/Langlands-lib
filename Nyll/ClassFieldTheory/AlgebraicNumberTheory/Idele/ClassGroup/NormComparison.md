# Relative and ordinary idele-class norms

Module `Nyll.ClassFieldTheory.AlgebraicNumberTheory.Idele.ClassGroup.NormComparison`, copied unchanged from the Lean library NYLL. The origin of the file is given at the end of this page.

The library has two presentations of the idele class group of a finite extension `L/K`: the relative one, `RelativeIdeleGroup.ClassGroup K L`, built from the units of `𝔸_K ⊗[K] L` with the determinant norm, and the ordinary class group `C_L` with the usual norm from `C_L` to `C_K`. The file proves product formulas for the relative class norm and shows that the two norms agree under the canonical isomorphism `C(𝔸_K ⊗[K] L) ≃ C_L`, so that results proved in relative coordinates can be stated with the usual norm.

## Main definitions and results

- `RelativeIdeleGroup.classEmbedding f`: for a `K`-embedding `f : L →ₐ[K] M` of finite extensions, the induced map of relative idele class groups.
- `classInclusion_ideleClassNorm_eq_prod_conjugates`: if `L/K` is Galois, the image in `C(𝔸_K ⊗ L)` of the norm of `c` is the product of the Galois conjugates `σ • c`.
- `classInclusion_ideleClassNorm_eq_prod_embeddings`: if `K ⊆ L ⊆ M` with `M/K` Galois, the image in `C(𝔸_K ⊗ M)` of the norm of `c` is the product over all `K`-embeddings `f : L → M` of `classEmbedding f c`. No normality of `L/K` is assumed.
- `classInclusion_ideleClassNorm_eq_prod_galoisCosets`: the same product indexed by the cosets of `Gal(M/K)` modulo the subgroup fixing `L`.
- `ordinaryIdeleClassNorm_relativeIdeleClassBaseChange`: for number fields `K ⊆ L`, the ordinary norm `ideleClassNorm K L` composed with `relativeIdeleClassBaseChangeMulEquiv` is the relative class norm.
- `ordinaryIdeleClassNorm_range_eq_relative`: the two norms have the same image in `C_K`.

## Proofs

Each class-level formula is the descent through the quotient by principal ideles of the corresponding idele-level formula proved in imported files (`inclusion_norm_eq_prod_conjugates`, `inclusion_norm_eq_prod_embeddings`, `norm_relativeIdeleBaseChangeMulEquiv`). The coset form reindexes the product by the bijection `cosetEquivEmbedding` between cosets and embeddings.

## Points to watch

- In the product formulas `L` and `M` are only assumed to be fields finite over the number field `K`; the comparison with the ordinary norm requires `L` to be a number field and does not use the Galois hypothesis of the section.

## Origin of the file

Copied unchanged from the Lean library NYLL (https://github.com/n-yamaguchi-0729/NYLL), commit `fe40c03df1b2b195053fdd63305571d97c73ce48`, file `Nyll/ClassFieldTheory/AlgebraicNumberTheory/Idele/ClassGroup/NormComparison.lean`: the Lean file is the source byte for byte (SHA-256 `9c0783ecb9454ccd3360fdaa87088c45c72279371f1897f5517e5d319ddf47ff`). That library is distributed under the Apache License, Version 2.0; its licence and notice are kept with the Library's licences.
