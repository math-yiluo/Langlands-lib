# Openness of the norm group for fields in arbitrary universes

Module `Nyll.ClassFieldTheory.GlobalClassFieldTheory.GlobalClassFields.UniverseNormConductor`, copied unchanged from the Lean library NYLL. The origin of the file is given at the end of this page.

Let L/K be a finite Galois extension of number fields, with K and L in independent universes u and v. The file shows that the norm group N(C_L) ⊆ C_K is open. So it has a defining modulus, and it is a conductorial subgroup.

## Main results

- `ideleClassNorm_range_isOpen_universe`: the range of the idele-class norm C_L → C_K is open.
- `ideleClassNormConductorialSubgroup_universe K L`: that range, as a `ConductorialSubgroup K` (the library's notion: a subgroup with a defining modulus). The modulus comes from openness.
- `ideleClassNormConductorialSubgroup_universe_eq_native`: for fields in `Type` it agrees, by `rfl`, with the existing `ideleClassNormConductorialSubgroup`.

## Proof

Replace K and L by isomorphic copies in `Type` (`Shrink`). By imported results, the induced homeomorphism of idele class groups carries one norm range onto the other, and the norm range of the copies is open. Openness pulls back. The norm map itself is unchanged; only the existence proof of a modulus is transported.

## Origin of the file

Copied unchanged from the Lean library NYLL (https://github.com/n-yamaguchi-0729/NYLL), commit `fe40c03df1b2b195053fdd63305571d97c73ce48`, file `Nyll/ClassFieldTheory/GlobalClassFieldTheory/GlobalClassFields/UniverseNormConductor.lean`: the Lean file is the source byte for byte (SHA-256 `2deca687ad898d2c7e1721921f5b8fb30ccc26cd3c12ad1f5b58325e831e43d3`). That library is distributed under the Apache License, Version 2.0; its licence and notice are kept with the Library's licences.
