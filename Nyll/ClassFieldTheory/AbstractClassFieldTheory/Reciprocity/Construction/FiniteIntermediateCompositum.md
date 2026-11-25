# Composita of finite intermediate fields

Module `Nyll.ClassFieldTheory.AbstractClassFieldTheory.Reciprocity.Construction.FiniteIntermediateCompositum`, copied unchanged from the Lean library NYLL. The origin of the file is given at the end of this page.

In the abstract setting a field is a closed subgroup of a group `G` carrying a topology, and a `FiniteIntermediateField E K` is a closed subgroup between `E` and `K` of finite index over `K`. This file supplies two closure facts used in the proof of the universal norm-descent lemma.

- `FiniteIntermediateField.compositum M N`: the compositum of two finite intermediate fields of `E / K`, defined on the Galois side as the intersection `M ⊓ N`; it is again finite over `K`. The lemmas `compositum_le_left` and `compositum_le_right` say it contains both fields, that is, lies below both as a subgroup.
- `FiniteIntermediateField.absoluteFinite`: if `K` is of finite index over the base field `G`, every finite intermediate field of `E / K` is of finite index over the base field as well, by finiteness in a tower.

Inclusions of fields are reversed inclusions of subgroups throughout: a larger field is a smaller subgroup.

## Origin of the file

Copied unchanged from the Lean library NYLL (https://github.com/n-yamaguchi-0729/NYLL), commit `fe40c03df1b2b195053fdd63305571d97c73ce48`, file `Nyll/ClassFieldTheory/AbstractClassFieldTheory/Reciprocity/Construction/FiniteIntermediateCompositum.lean`: the Lean file is the source byte for byte (SHA-256 `40d9abe830b92010a9d4e83b4ba548ccf40e48979b5ed85b983954762882c0ac`). That library is distributed under the Apache License, Version 2.0; its licence and notice are kept with the Library's licences.
