# Naturality of the big Hilbert norm group under field isomorphisms

Module `Nyll.ClassFieldTheory.GlobalClassFieldTheory.GlobalClassFields.BigHilbertClassFieldNaturality`, copied unchanged from the Lean library NYLL. The origin of the file is given at the end of this page.

Let `e : K ≃ₐ[ℚ] M` be an isomorphism of number fields. Transport of ideles along `e` preserves integrality at the finite places and positivity at the real places. The file deduces that the induced map of idele class groups carries the big-Hilbert norm subgroup of `K` onto that of `M`. This gives compatible isomorphisms of the big-Hilbert reciprocity quotients and of the narrow class groups, with explicit formulas on idele representatives.

## Main results

- `bigHilbertClassFieldNormSubgroup_map_ideleClassCongr`: the image of `bigHilbertClassFieldNormSubgroup K` under `ideleClassCongr e` is `bigHilbertClassFieldNormSubgroup M`.
- `bigHilbertClassFieldQuotientCongr e`: the induced isomorphism `C_K ⧸ H_K ≃* C_M ⧸ H_M`; `..._mk` says it acts on a class `c` through `ideleClassCongr e`.
- `bigHilbertNarrowClassGroupCongr e`: the induced isomorphism of narrow class groups `RayClass.NarrowClassGroup K ≃* RayClass.NarrowClassGroup M`.
- `bigHilbertClassFieldQuotientEquivNarrowClassGroup_naturality` (and `_hom`): the identifications of the quotients with the narrow class groups commute with these transports.
- `bigHilbertNarrowClassGroupCongr_mk` and `bigHilbertNarrowClassGroupCongr_naturality`: on the narrow class of an idele `a`, the transport gives the narrow class of `ideleCongr e a`.

## Proof

Private lemmas compute the archimedean components of transported adeles through base change from `ℚ`. They show that the completion maps at infinite places commute with the real embeddings, so positivity at real places is preserved in both directions. With the imported integrality statement and the transport of principal ideles, the narrow denominator of `K` (positive integral ideles times principal ideles) maps exactly onto that of `M`, and the congruence subgroups correspond.

## Points to watch

- `bigHilbertNarrowClassGroupCongr` is defined through the big-Hilbert quotients and their identification with the narrow class groups, not directly on fractional ideals; its value on idele representatives is a theorem.

## Origin of the file

Copied unchanged from the Lean library NYLL (https://github.com/n-yamaguchi-0729/NYLL), commit `fe40c03df1b2b195053fdd63305571d97c73ce48`, file `Nyll/ClassFieldTheory/GlobalClassFieldTheory/GlobalClassFields/BigHilbertClassFieldNaturality.lean`: the Lean file is the source byte for byte (SHA-256 `688748b64538ba18883d34dc248a4dc456435b7c7aa32dd32c1c14bfe665d72d`). That library is distributed under the Apache License, Version 2.0; its licence and notice are kept with the Library's licences.
