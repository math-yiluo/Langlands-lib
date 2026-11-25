# Naturality of the transfer under a quotient map

Module `Nyll.ClassFieldTheory.AbstractClassFieldTheory.Reciprocity.Construction.TransferNaturality`, copied unchanged from the Lean library NYLL. The origin of the file is given at the end of this page.

Pure group theory, with no fields or modules, used for the compatibility of reciprocity with the transfer in the abstract class field theory of the library. Let `f : P →* Q` be a surjective homomorphism and `H` a subgroup of `P` that contains the kernel of `f`. Then `f` identifies the left cosets of `H` with those of `f(H)`, and Mathlib's transfer (`MonoidHom.transfer`) commutes with the maps that `f` induces on abelianizations.

## Main definitions and results

- `leftCosetEquivMapOfSurjective f hf H hker`: the bijection `P/H ≃ Q/f(H)`, `pH ↦ f(p)f(H)`. It is compatible with left multiplication (`leftCosetEquivMapOfSurjective_mk`, `..._smul`).
- `leftTransversalMapOfSurjective`: a left transversal of `H` pushed forward to a left transversal of `f(H)`; its representatives are the images of the original ones (`leftTransversalMapOfSurjective_apply`).
- `abelianization_transfer_natural_of_surjective`: if moreover `H` has finite index, then `Ver(f(H)) ∘ f^ab = (f|_H)^ab ∘ Ver(H)` as maps `P^ab → f(H)^ab`, where `Ver` is `MonoidHom.transfer` applied to the abelianization map of the subgroup (`Abelianization.of`) and then factored through the abelianization of the ambient group (`Abelianization.lift`).
- `abelianization_transfer_congr_subgroup`: for equal subgroups `H = J` of finite index, the two transfers agree after the canonical identification `H^ab ≃ J^ab`.

## Proofs

The naturality is checked on generators. The transfer of `p` is computed with any left transversal `T` and with its translate `p·T`. Both are pushed forward along `f`, and the defining product for `H` maps term by term onto the one for `f(H)` (private lemmas on transversal differences).

## Watch for

The hypothesis `ker f ≤ H` is essential: it is what makes the coset map a bijection and gives `f(H)` the same finite index.

## Origin of the file

Copied unchanged from the Lean library NYLL (https://github.com/n-yamaguchi-0729/NYLL), commit `fe40c03df1b2b195053fdd63305571d97c73ce48`, file `Nyll/ClassFieldTheory/AbstractClassFieldTheory/Reciprocity/Construction/TransferNaturality.lean`: the Lean file is the source byte for byte (SHA-256 `076c9a15cb5158f6a7b32ef3f2329d42511f3bb8f0e9f085107ee347b3557979`). That library is distributed under the Apache License, Version 2.0; its licence and notice are kept with the Library's licences.
