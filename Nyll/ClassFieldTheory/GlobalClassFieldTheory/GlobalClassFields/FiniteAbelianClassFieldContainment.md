# Containment of finite abelian extensions and their norm groups

Module `Nyll.ClassFieldTheory.GlobalClassFieldTheory.GlobalClassFields.FiniteAbelianClassFieldContainment`, copied unchanged from the Lean library NYLL. The origin of the file is given at the end of this page.

For finite abelian extensions L₁ and L₂ of a number field K, this file proves that L₁ embeds into L₂ over K if and only if the idèle-class norm group of L₂/K is contained in that of L₁/K. This is the order-reversing half of the global class field correspondence, stated for actual field extensions rather than for subgroups of an absolute Galois group. Isomorphism over K is likewise characterized by equality of norm groups.

## Main definitions and results

- `closedFiniteIndexClassFieldBaseEmbedding` and `closedFiniteIndexClassFieldCompatibleEmbedding H hclosed E`: for a closed subgroup H of finite index in C_K, the embedding of K into ℚ̄ used by the class field selected by H, and a chosen extension of it to an embedding of E.
- `closedFiniteIndexClassFieldEmbeddedAbelianSubextension`: E, for E/K abelian, as a finite abelian subextension over the same base subgroup as the class field of H. `ordinaryIdeleClassNormSubgroup_embeddedAbelianSubextension` identifies its abstract norm subgroup with the norm group of E/K, transported to the selected copy of K.
- `embeddedAbelianSubextension_le_closedFiniteIndexClassFieldSubextension`: if H is contained in the norm group of E/K, the embedded subextension lies below the one selected by H.
- `finiteAbelianExtensionEmbeddingIntoClosedFiniteIndexClassField`: under the same hypothesis, a K-algebra map from E into the class field `closedFiniteIndexClassField H hclosed`.
- `finiteAbelianExtensionEquivClosedFiniteIndexNormClassField`: every finite abelian E/K is K-isomorphic to the class field selected by its own norm group.
- `ideleClassNorm_range_le_of_algHom` and `finiteAbelianExtensionEmbeddingOfNormRangeLE`: the two directions of the criterion, combined in `nonempty_algHom_iff_ideleClassNorm_range_le`.
- `nonempty_algEquiv_iff_ideleClassNorm_range_eq`: L₁ ≃ₐ[K] L₂ exists if and only if the two norm groups are equal.

## Proof

E is placed in ℚ̄ compatibly with the copy of K used by the class field of H. The abstract classification of finite abelian subextensions by norm subgroups (`le_iff_ordinaryIdeleClassNormSubgroup_le`) then gives an inclusion of fixing subgroups. This inclusion restricts the embedding of E so that it lands in the class field. The isomorphism with the class field of the norm group follows by counting degrees. It uses the abelian norm index theorem, that the norm group of E/K has index [E : K] in C_K (`ideleClassNorm_index_eq_finrank_abelian`), and the imported degree formula `closedFiniteIndexClassField_finrank_eq_index`. The direction from an embedding of L₁ into L₂ to the inclusion of norm groups is transitivity of norms in the tower K ⊆ L₁ ⊆ L₂.

## Points to watch

- Both extensions must be finite abelian (`IsAbelianGalois`), and the embedding of E into ℚ̄ is a non-canonical choice made through `Classical.choose`.

## Origin of the file

Copied unchanged from the Lean library NYLL (https://github.com/n-yamaguchi-0729/NYLL), commit `fe40c03df1b2b195053fdd63305571d97c73ce48`, file `Nyll/ClassFieldTheory/GlobalClassFieldTheory/GlobalClassFields/FiniteAbelianClassFieldContainment.lean`: the Lean file is the source byte for byte (SHA-256 `bda89359baa186c715d73435fc7599a69add88fb63e21e4627c64e47e56cc7c6`). That library is distributed under the Apache License, Version 2.0; its licence and notice are kept with the Library's licences.
