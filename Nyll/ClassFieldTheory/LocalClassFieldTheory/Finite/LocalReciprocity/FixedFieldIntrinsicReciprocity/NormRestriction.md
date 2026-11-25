# Norm–restriction compatibility of the local Artin map

Module `Nyll.ClassFieldTheory.LocalClassFieldTheory.Finite.LocalReciprocity.FixedFieldIntrinsicReciprocity.NormRestriction`, copied unchanged from the Lean library NYLL. The origin of the file is given at the end of this page.

Let `K'/K` be a finite separable extension of nonarchimedean local fields, the valuation of `K'` extending that of `K`. Let `L/K` and `L'/K'` be finite abelian extensions with `L ⊆ L'`, compatibly with `K ⊆ K' ⊆ L'`. The file proves the standard functoriality of local reciprocity: the Artin map of `L'/K'`, followed by restriction to `L`, equals the Artin map of `L/K` composed with the norm from `K'^×` to `K^×`.

## Main results

- `abelianLocalArtinMonoidHom_norm_restriction`: as homomorphisms `K'^× → Gal(L/K)`, the composite of `abelianLocalArtinMonoidHom K' L'` with restriction `Gal(L'/K') → Gal(L/K)` equals `abelianLocalArtinMonoidHom K L` composed with `normUnits K K'`.
- `ambientEmbeddedNormResidueElement_norm_restriction`: the same identity for the ambient norm-residue elements. These are computed by realizing all fields inside `K^sep`, for any embedding `j : L' →ₐ[K] K^sep` and any choice of the isomorphisms of separable closures for `K` and `K'`.

## Helper results

- `AmbientEmbeddedFixedFieldPresentation.quotientRestriction`: take fixed-field presentations of `L/K` and `L'/K'` whose subgroups are nested, and a homomorphism `Gal(L'/K') → Gal(L/K)` compatible with the embeddings (hypotheses `hbase`, `hcompat`). Under the presentations' quotient isomorphisms, it agrees with the abstract restriction `normResidueNaturalityAbelianizedRestriction`.
- `AmbientEmbeddedFixedFieldPresentation.fixedFieldNormResidueTransport`: under the presentations, abstract restriction carries the abstract fixed-field symbol of `a` for `L'/K'` to that of `normUnits K K' a` for `L/K`. It rests on `abstractFixedFieldNormResidueSymbol_norm_restriction` and on `normUnits_mapEquiv`.

## Proof

Choose an embedding `j : L' → K^sep` (`IsSepClosed.lift`), the identity of `K^sep` for `K`, and the isomorphism of separable closures for `K'` given by `IsSepClosure.equiv`. By `abelianLocalArtin_eq_ambientEmbeddedNormResidueSymbol_of_equiv`, both Artin maps equal the corresponding ambient norm-residue elements. The ambient elements satisfy the identity because the norm–restriction naturality of the abstract symbol in the class formation over `K` is transported through the two presentations.

## Points to watch

- Only `K` and `K'` carry local-field structures; `L` and `L'` are plain fields. `K'/K` must be separable, and the fields live in `Type`.
- Both helper theorems take the compatibility of the embeddings as an explicit hypothesis (`hbase`), and `quotientRestriction` also that of the restriction map (`hcompat`); the main theorems discharge them for their canonical choices.

## Origin of the file

Copied unchanged from the Lean library NYLL (https://github.com/n-yamaguchi-0729/NYLL), commit `fe40c03df1b2b195053fdd63305571d97c73ce48`, file `Nyll/ClassFieldTheory/LocalClassFieldTheory/Finite/LocalReciprocity/FixedFieldIntrinsicReciprocity/NormRestriction.lean`: the Lean file is the source byte for byte (SHA-256 `926943f744c05013ffc0cf898082e2147c542c9efc4a82f39cb7b6929109f60b`). That library is distributed under the Apache License, Version 2.0; its licence and notice are kept with the Library's licences.
