# The finite abelian class field correspondence on ordinary idèle class groups

Module `Nyll.ClassFieldTheory.GlobalClassFieldTheory.GlobalClassFields.FiniteAbelianClassFieldCorrespondence`, copied unchanged from the Lean library NYLL. The origin of the file is given at the end of this page.

The library's abstract class field theory works with closed subgroups of Gal(ℚ̄/ℚ), where ℚ̄ is `SeparableClosure ℚ`. Norm subgroups there live in the fixed part of the rational idèle-class representation. This file takes a finite abstract base field K, that is, a closed subgroup of Gal(ℚ̄/ℚ) of finite index, and lets F be its actual fixed field. Through a canonical equivalence, the norm subgroup of each finite abelian subextension of K becomes a subgroup of the ordinary idèle class group C_F, and the abstract classification is restated there.

## Main definitions and results

- `ordinaryIdeleClassNormSubgroup K L`: for `L : FiniteAbelianSubextension K.field`, the abstract norm subgroup of L transported to C_F by `rationalAbstractFixedFieldIdeleClassEquivFixed`. It is an additive subgroup of `Additive (IdeleClassGroup F)`.
- `ordinaryIdeleClassNormSubgroup_eq_actualNormRange`: this subgroup equals the range of the idèle-class norm from E to F, where E is the actual relative fixed field of L, which is shown to be a finite abelian extension of F.
- `le_iff_ordinaryIdeleClassNormSubgroup_le`: L₁ ≤ L₂ as subextensions if and only if the norm subgroup of L₂ is contained in that of L₁. Hence `ordinaryIdeleClassNormSubgroup_injective`: a finite abelian subextension is determined by its norm subgroup.
- `ordinaryIdeleClassNormSubgroup_compositum`: the norm subgroup of a compositum is the intersection of the two norm subgroups.
- `ordinaryIdeleClassNormSubgroup_intersection`: the norm subgroup of an intersection of subextensions is the sum (join) of the two norm subgroups.

## Proof

The identification with the actual norm range is the imported comparison `map_rationalFiniteNormSubgroup_eq_ordinaryIdeleClassNormRange_concrete`. Each order and lattice statement is the corresponding abstract statement for `FiniteAbelianSubextension`, transported along an injective additive map. The abstract statements are applied to `rationalCyclotomicIdeleClassValuationData`, together with the imported fact `rationalIdeleClassRepresentation_satisfiesClassFieldAxiom` that the rational idèle-class representation satisfies the class field axiom.

## Points to watch

- The objects are the library's abstract finite fields and finite abelian subextensions, not Mathlib intermediate fields. The norm subgroups are written additively, as `AddSubgroup (Additive (IdeleClassGroup F))`.

## Origin of the file

Copied unchanged from the Lean library NYLL (https://github.com/n-yamaguchi-0729/NYLL), commit `fe40c03df1b2b195053fdd63305571d97c73ce48`, file `Nyll/ClassFieldTheory/GlobalClassFieldTheory/GlobalClassFields/FiniteAbelianClassFieldCorrespondence.lean`: the Lean file is the source byte for byte (SHA-256 `0117dfc4dd297d765c510ae392f16b24c6237a329cfce0be9f167fcd54596df5`). That library is distributed under the Apache License, Version 2.0; its licence and notice are kept with the Library's licences.
