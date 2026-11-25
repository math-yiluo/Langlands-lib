# The idele norm preserves the archimedean and absolute norms

Module `Nyll.ClassFieldTheory.AlgebraicNumberTheory.Idele.NormTopology.ArchimedeanNorm`, copied unchanged from the Lean library NYLL. The origin of the file is given at the end of this page.

Let L/K be a finite extension of number fields, and let `IdeleGroup.norm K L` be the norm map from the ideles of L to the ideles of K. This file proves that this map preserves the archimedean part of the absolute idele norm, and hence the whole absolute norm.

## Main results

- `IdeleGroup.archimedeanNorm_norm`: for an idele a of L, the archimedean norm ∏_v ‖·‖^(m_v) of the image of a in the ideles of K equals the archimedean norm of a, taken over the infinite places of L.
- `IdeleGroup.absoluteNorm_norm`: `absoluteNorm (norm K L a) = absoluteNorm a`. It combines the archimedean result with `finiteAbsoluteNorm_norm` from the imported file on the finite part.

The private helper lemmas say three things. Isometric ring isomorphisms preserve the norm of units. The field norm from ℂ to ℝ squares the absolute value. And for an infinite place W of L over v of K, the norm of x ∈ L_Wˣ down to K_v satisfies ‖N(x)‖^(m_v) = ‖x‖^(m_W), where m is 1 at a real place and 2 at a complex one.

## Proof

The local lemma is proved case by case: real over real, complex over real, and complex over complex. In the last case the identification of L_W with ℂ may have to be composed with complex conjugation, so that it is compatible with K_v ≅ ℂ. For the global statement, the v-component of the norm of a is the product of the local norms of the components at the places of L above v (`infiniteComponent_norm_eq_prod`). The local lemma then applies, and the product over all places of L is regrouped by the place of K below.

## Points to watch

- `IdeleGroup.norm`, `archimedeanNorm` and `absoluteNorm` are the library's own definitions. Its absolute norm is the reciprocal of the usual ∏_v |a_v|_v, and the identity holds in either normalization.
- No Galois hypothesis is needed. The extension must be finite and both fields must be number fields.

## Origin of the file

Copied unchanged from the Lean library NYLL (https://github.com/n-yamaguchi-0729/NYLL), commit `fe40c03df1b2b195053fdd63305571d97c73ce48`, file `Nyll/ClassFieldTheory/AlgebraicNumberTheory/Idele/NormTopology/ArchimedeanNorm.lean`: the Lean file is the source byte for byte (SHA-256 `6667fba4eeb4ca1bcefff2b3b171cd7d60fb80650eeb2fd5078174848bf06801`). That library is distributed under the Apache License, Version 2.0; its licence and notice are kept with the Library's licences.
