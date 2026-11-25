# The local Artin map agrees with the ambient norm-residue symbol

Module `Nyll.ClassFieldTheory.LocalClassFieldTheory.Finite.LocalReciprocity.FixedFieldIntrinsicReciprocity.AmbientPrimeComparison`, copied unchanged from the Lean library NYLL. The origin of the file is given at the end of this page.

Let `K ⊆ F ⊆ E` with `K`, `F` nonarchimedean local fields, `F/K` finite separable with compatible valuations, and `E/F` finite abelian. Fix a `K`-embedding `j : E →ₐ[K] K^sep` and an `F`-isomorphism `e` from the separable closure of `F` to `K^sep`. The file shows that the local Artin map of `E/F` coincides pointwise with the norm-residue value obtained by realizing `F` and `E` as fixed fields of closed subgroups of `Gal(K^sep/K)` (`ambientEmbeddedNormResidueElement`). So the reciprocity map of `E/F` can be computed in the ambient Galois group of `K`.

## Main results

- `exists_localArtin_ambientEmbedded_prime`: every `z ∈ Gal(E/F)^ab` is the common value at one unit `x ∈ F^×` of `localArtinMonoidHom F E` and of `ambientEmbeddedNormResidueAbelianElement K F E j e`. The unit is `ambientEmbeddedPrimeWitness` from the imported witness-comparison file.
- `ambientEmbeddedNormResidueAbelianElement_eq_of_normClass_eq`: the ambient value of a unit depends only on its class modulo norms from `E`. The norm-class equality is transported to the abstract fixed fields (`normClass_mapEquiv`) and the corresponding statement for `abstractFixedFieldNormResidueSymbol` is applied.
- `abelianLocalArtin_eq_ambientEmbeddedNormResidueSymbol_of_equiv`: for every `a ∈ F^×`, `abelianLocalArtinMonoidHom F E a = ambientEmbeddedNormResidueElement K F E j e a`.

## Proof of the comparison

Given `a`, take a unit `x` at which both maps take the value `Artin(a)`. Composing `j` with the inverse of `e` gives an embedding of `E` into the separable closure of `F`; there the local Artin map equals the concrete norm-residue symbol (`localArtinMonoidHom_eq_of_embedding`), and the concrete reciprocity equivalence is injective on norm classes. Hence `a` and `x` have the same norm class, and the previous lemma finishes.

## Points to watch

- The result rests on the witness construction of the imported files and holds for the chosen `j` and `e`; it is stated for fields in `Type` (universe 0).
- `localArtinMonoidHom` takes values in the abelianization, `abelianLocalArtinMonoidHom` in `Gal(E/F)` itself; the main theorem is about the latter.

## Origin of the file

Copied unchanged from the Lean library NYLL (https://github.com/n-yamaguchi-0729/NYLL), commit `fe40c03df1b2b195053fdd63305571d97c73ce48`, file `Nyll/ClassFieldTheory/LocalClassFieldTheory/Finite/LocalReciprocity/FixedFieldIntrinsicReciprocity/AmbientPrimeComparison.lean`: the Lean file is the source byte for byte (SHA-256 `7f204fdf010e81d321209afd13a437714bbc24b902210b1fbf1aa627dfe010f1`). That library is distributed under the Apache License, Version 2.0; its licence and notice are kept with the Library's licences.
