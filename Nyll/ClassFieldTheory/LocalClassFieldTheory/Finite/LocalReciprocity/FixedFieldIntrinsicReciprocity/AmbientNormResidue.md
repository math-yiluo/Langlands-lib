# The norm-residue value of an embedded extension, computed in the ambient Galois group

Module `Nyll.ClassFieldTheory.LocalClassFieldTheory.Finite.LocalReciprocity.FixedFieldIntrinsicReciprocity.AmbientNormResidue`, copied unchanged from the Lean library NYLL. The origin of the file is given at the end of this page.

Let `K ⊆ F ⊆ E` with `K`, `F` nonarchimedean local fields, `F/K` finite separable with the valuation of `F` extending that of `K`, and `E/F` finite Galois. Given a `K`-embedding `j : E →ₐ[K] K^sep` into the separable closure of `K` and an `F`-algebra isomorphism `e` from the separable closure of `F` to `K^sep` (with `F` acting through `j`), the file realizes `F` and `E` as fixed fields of closed subgroups of `Gal(K^sep/K)` and defines the norm-residue value of a unit `a ∈ F^×` in `Gal(E/F)^ab` through the abstract class-formation symbol over `K`.

## Definitions

- `ambientEmbeddedSeparableClosureEquiv K F E j`: the type of such isomorphisms `e`.
- `AmbientEmbeddedFixedFieldPresentation K F E j`: a structure recording an embedding of `F` (equal to `j` restricted to `F`), a finite abstract field `base` whose group is the fixing subgroup of the image of `F`, a finite Galois subextension `extension` whose group fixes the image of `E`, a `K`-isomorphism of `F` with the abstract fixed field of `base` compatible with the embedding, and an isomorphism of the extension quotient with `Gal(E/F)` compatible with `j`.
- `fixedFieldQuotientEquiv` and `abelianizedTransport`: the extension quotient identified with the Galois group of the relative fixed field, and the resulting additive equivalence of its abelianization with `Gal(E/F)^ab`.
- `normResidueAbelianElement P a`: move `a` to the abstract fixed field, apply `abstractFixedFieldNormResidueSymbol` for the class formation of units of `K^sep` (with `localResidueDatum K` and `localHenselianValuation K`), and transport the value to `Gal(E/F)^ab`. `normResidueAbelianElement_apply` unfolds this by `rfl`.
- `ambientEmbeddedFixedFieldPresentation K F E j e`: the canonical presentation by the fixing subgroups of the images of `F` and `E`; normality of the extension subgroup and finiteness of its quotient are taken from imported results, which use `e`.
- `ambientEmbeddedNormResidueAbelianElement`: the value for the canonical presentation.
- `ambientEmbeddedNormResidueElement`: when `E/F` is abelian (`IsAbelianGalois`), the same value in `Gal(E/F)` via the abelianization of a commutative group.

## Points to watch

- The file contains only definitions and an unfolding lemma; no property of the symbol (homomorphism, reciprocity, independence of `j` or `e`) is proved here.
- The fields `K`, `F`, `E` live in `Type` (universe 0).
- `FiniteAbstractField`, `FiniteGaloisSubextension` and the fixed-field norm-residue symbol are the library's own class-formation notions.

## Origin of the file

Copied unchanged from the Lean library NYLL (https://github.com/n-yamaguchi-0729/NYLL), commit `fe40c03df1b2b195053fdd63305571d97c73ce48`, file `Nyll/ClassFieldTheory/LocalClassFieldTheory/Finite/LocalReciprocity/FixedFieldIntrinsicReciprocity/AmbientNormResidue.lean`: the Lean file is the source byte for byte (SHA-256 `5963b187e494fd6a05e063b59d734f5a59f9ed15986da3136e3ab1740744c382`). That library is distributed under the Apache License, Version 2.0; its licence and notice are kept with the Library's licences.
