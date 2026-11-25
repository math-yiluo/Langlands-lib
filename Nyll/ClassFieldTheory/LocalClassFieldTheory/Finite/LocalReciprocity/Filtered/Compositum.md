# Filtered reciprocity for a compositum

Module `Nyll.ClassFieldTheory.LocalClassFieldTheory.Finite.LocalReciprocity.Filtered.Compositum`, copied unchanged from the Lean library NYLL. The origin of the file is given at the end of this page.

Let `K` be a nonarchimedean local field and `E₁, E₂, F` finite abelian Galois extensions inside `SeparableClosure K`, with `E₁, E₂ ≤ F` and `E₁ ⊔ E₂ = F`.

`filteredLocalReciprocity_of_compositum`: fix a real `t`. If for `E₁` both the Artin principal-unit step group and the upper ramification group at `t` are trivial, and for `E₂` the two groups at `t` coincide, then they coincide for `F`.

Proof: the restriction maps from `Gal(F / K)` to `Gal(E₁ / K)` and `Gal(E₂ / K)` are jointly injective (`intermediateFieldRestrictNormalHom_prod_injective_of_sup_eq`). Both filtrations are compatible with restriction (`artinPrincipalUnitStepGroup_map_intermediateFieldRestrict`, `localUpperRamificationGroup_map_restrict`), and a subgroup lemma concludes.

The three conditions on `E₁` and `E₂` (`hArtin₁`, `hUpper₁`, `hfiltered₂`) are hypotheses; the last is the filtered reciprocity statement for `E₂`, assumed here. The header has in mind an unramified `E₁` and `t ≥ 0`, but the theorem asks only for the stated vanishing, at any real `t`. The base field is `K : Type`, in universe `0`.

## Origin of the file

Copied unchanged from the Lean library NYLL (https://github.com/n-yamaguchi-0729/NYLL), commit `fe40c03df1b2b195053fdd63305571d97c73ce48`, file `Nyll/ClassFieldTheory/LocalClassFieldTheory/Finite/LocalReciprocity/Filtered/Compositum.lean`: the Lean file is the source byte for byte (SHA-256 `99604a2b653a9f812179223a8b460247950bef61a43f104ac7663bf780319032`). That library is distributed under the Apache License, Version 2.0; its licence and notice are kept with the Library's licences.
