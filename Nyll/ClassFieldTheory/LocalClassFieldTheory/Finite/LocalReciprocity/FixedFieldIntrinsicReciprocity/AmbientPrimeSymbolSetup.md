# The norm-residue symbol of the prime witness: setup

Module `Nyll.ClassFieldTheory.LocalClassFieldTheory.Finite.LocalReciprocity.FixedFieldIntrinsicReciprocity.AmbientPrimeSymbolSetup`, copied unchanged from the Lean library NYLL. The origin of the file is given at the end of this page.

Let `K ⊆ F ⊆ E` with `K`, `F` nonarchimedean local fields, `F/K` finite separable with compatible valuations, `E/F` finite abelian, a `K`-embedding `j : E →ₐ[K] K^sep` and an `F`-isomorphism `e` from the separable closure of `F` to `K^sep`. For `z ∈ Gal(E/F)^ab` the imported file chooses a unit `ambientEmbeddedPrimeWitness K F E j e z` of `F` (built from a prime element) and a Frobenius target. This file states what it means for the ambient norm-residue symbol of that witness to be the expected Frobenius element, and shows that this formula makes the transported value equal to the target.

## Definitions and results

- `ambientEmbeddedPrimeTransportValue K F E j e z`: the value of `abstractFixedFieldNormResidueSymbol` for `K` on the witness, after realizing `F` and `E` as fixed fields of closed subgroups of `Gal(K^sep/K)`, transported to `Gal(E/F)^ab`.
- `ambientEmbeddedPrimeSymbolProperty K F E j e z`: a proposition. One lifts `z` to the extension quotient of the intrinsic presentation of `E/F` (through the embedding of `E` into the separable closure of `F` given by `j` and `e`), chooses a Frobenius element `σ` over `F` restricting to it, and moves `σ` to the ambient field (`intrinsicFrobeniusElementToAmbientEmbeddedField`). The proposition says that the ambient symbol of the witness equals the abelianized Frobenius restriction of the moved element.
- `ambientEmbeddedPrimeTransportValue_eq_target_of_symbol`: if that formula holds (hypothesis `_hsymbol`), then the transported value equals `ambientEmbeddedPrimeTarget K F E j e z`. The proof is a single application of `abelianizationCongr_symm_eq_primeTarget`.

## Points to watch

- `ambientEmbeddedPrimeSymbolProperty` only defines a proposition; the file does not prove it.
- The main theorem is conditional: its hypothesis `_hsymbol` is exactly the symbol formula, to be supplied elsewhere.
- The lift of `z` and the Frobenius element are made with `Classical.choose`; the objects depend on these choices and on `j` and `e`.
- Frobenius elements, `localResidueDatum` and `localHenselianValuation` are the library's own class-formation notions; the fields live in `Type`.

## Origin of the file

Copied unchanged from the Lean library NYLL (https://github.com/n-yamaguchi-0729/NYLL), commit `fe40c03df1b2b195053fdd63305571d97c73ce48`, file `Nyll/ClassFieldTheory/LocalClassFieldTheory/Finite/LocalReciprocity/FixedFieldIntrinsicReciprocity/AmbientPrimeSymbolSetup.lean`: the Lean file is the source byte for byte (SHA-256 `b1068c1f1048106d9e4e921e03bd1d42330153da69a9d5321ce667ebcaba9055`). That library is distributed under the Apache License, Version 2.0; its licence and notice are kept with the Library's licences.
