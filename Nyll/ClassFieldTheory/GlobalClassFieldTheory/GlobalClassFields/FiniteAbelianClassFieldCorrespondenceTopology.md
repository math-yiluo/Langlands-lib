# Topology and index of ordinary norm subgroups

Module `Nyll.ClassFieldTheory.GlobalClassFieldTheory.GlobalClassFields.FiniteAbelianClassFieldCorrespondenceTopology`, copied unchanged from the Lean library NYLL. The origin of the file is given at the end of this page.

This file continues the finite abelian class field correspondence on ordinary idèle class groups. Let K be a finite abstract base field, that is, a closed subgroup of finite index in Gal(ℚ̄/ℚ), and let L be a finite abelian subextension of it. The norm subgroup attached to L is the range of an actual idèle-class norm map between number fields. So it is open, closed and of finite index, and its index is the degree.

## Main definitions and results

- `ordinaryIdeleClassNormBase K` and `ordinaryIdeleClassNormExtension K L`: named abbreviations for the fixed field F of K and the relative fixed field E of L. They come with global instances: E/F finite, both number fields, E/F abelian Galois.
- `ordinaryIdeleClassNormSubgroup_eq_namedNormRange`: the norm subgroup of L equals the range of the idèle-class norm from C_E to C_F, restated with these names.
- `ordinaryIdeleClassNormSubgroup_isOpen`, `ordinaryIdeleClassNormSubgroup_isClosed` and `ordinaryIdeleClassNormSubgroup_finiteIndex`: the norm subgroup is open, closed and of finite index in C_F.
- `ordinaryIdeleClassNormSubgroup_index_eq_finrank`: its index equals [E : F].

Each result rewrites by the norm-range identification and applies the corresponding imported fact about idèle-class norm ranges. The index statement uses the abelian norm index theorem `ideleClassNorm_index_eq_finrank_abelian`.

## Points to watch

- The subgroups are additive subgroups of `Additive (IdeleClassGroup F)`, and the topology is the one this type carries.

## Origin of the file

Copied unchanged from the Lean library NYLL (https://github.com/n-yamaguchi-0729/NYLL), commit `fe40c03df1b2b195053fdd63305571d97c73ce48`, file `Nyll/ClassFieldTheory/GlobalClassFieldTheory/GlobalClassFields/FiniteAbelianClassFieldCorrespondenceTopology.lean`: the Lean file is the source byte for byte (SHA-256 `bffcd7e63155944c251ffa2c5ccd87038823b4006b9e064e2f5ed527cad942b3`). That library is distributed under the Apache License, Version 2.0; its licence and notice are kept with the Library's licences.
