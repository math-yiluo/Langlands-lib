# Norm-open subgroups are open in the idele class group

Module `Nyll.ClassFieldTheory.GlobalClassFieldTheory.Reciprocity.IdeleClassNormTopology`, copied unchanged from the Lean library NYLL. The origin of the file is given at the end of this page.

Let ℚ̄ = `SeparableClosure ℚ`, and let K be a closed subgroup of finite index in Gal(ℚ̄/ℚ), with abstract fixed field F. The abstract class formation `rationalIdeleClassRepresentation` carries a norm topology on its K-fixed part: a subgroup is norm-open when it contains the norm subgroup of some finite Galois subextension. This file shows that such a subgroup, moved to the idele class group C_F of the actual number field F, is open for the usual topology of C_F.

## Main results

- `rationalTransportedNormSubgroup K H`: the image of an additive subgroup H of the K-fixed part in `Additive (IdeleClassGroup F)`, under the inverse of the fixed-part isomorphism `rationalAbstractFixedFieldIdeleClassEquivFixed`.
- `rationalNormOpenSubgroup_isOpen`: if H is norm-open (`IsNormOpen`), its transport is an open subset of C_F.

## Proof

A norm-open H contains `finiteNormSubgroup` of some `FiniteGaloisSubextension` E/F (by `normTopology_addSubgroup_isOpen_iff`). That subgroup is carried to the range of the idele class norm from C_E to C_F, by the result of the file on finite norm quotients. This range is open by `GlobalClassFields.ideleClassNorm_range_isOpen`. A subgroup that contains an open subgroup is open.

## Points to watch

- Only the base field ℚ is treated, and only one direction: norm-open implies open. The converse is not stated here.
- The finite-index condition on K is an instance argument, written as finiteness of a quotient by `extensionSubgroup`. The `NumberField` structure on F is built with `let` inside the statement.
- A local instance gives `IdeleClassGroup F` the quotient commutative group structure by the principal ideles.

## Origin of the file

Copied unchanged from the Lean library NYLL (https://github.com/n-yamaguchi-0729/NYLL), commit `fe40c03df1b2b195053fdd63305571d97c73ce48`, file `Nyll/ClassFieldTheory/GlobalClassFieldTheory/Reciprocity/IdeleClassNormTopology.lean`: the Lean file is the source byte for byte (SHA-256 `c2706d571d8a2bdb41a240950ba1f02bb3bf458c86114cf278c9cd266710918c`). That library is distributed under the Apache License, Version 2.0; its licence and notice are kept with the Library's licences.
