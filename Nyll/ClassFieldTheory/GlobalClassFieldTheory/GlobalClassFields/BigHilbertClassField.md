# The norm group of the big Hilbert class field

Module `Nyll.ClassFieldTheory.GlobalClassFieldTheory.GlobalClassFields.BigHilbertClassField`, copied unchanged from the Lean library NYLL. The origin of the file is given at the end of this page.

For a number field `K`, the big (narrow) Hilbert class field corresponds to the ray modulus with zero finite part in its narrow form, `RayClass.Modulus.narrowOfFinite 0`. This file defines the corresponding subgroup of the idele class group `C_K` and records its basic properties. The field itself is not constructed here.

- `bigHilbertClassFieldNormSubgroup`: the congruence subgroup of that modulus; it is normal and of finite index (instances) and closed (`..._isClosed`).
- `bigHilbertClassFieldQuotientEquivNarrowClassGroup`: `C_K ⧸ bigHilbertClassFieldNormSubgroup ≃* RayClass.NarrowClassGroup K`.
- `bigHilbertClassFieldConductorialSubgroup`: the subgroup packaged with this defining modulus (`..._isDefiningModulus`).
- `bigHilbertClassFieldNormSubgroup_le_iff_narrowFiniteConductor_eq_zero`: a conductorial subgroup contains it iff its narrow finite conductor is `0`.
- `bigHilbertClassField_narrowFiniteConductor`: its own narrow finite conductor is `0`.

The module docstring says that the description of the big Hilbert class field as a maximal unramified extension follows from these facts together with the conductor–ramification criterion; that statement is not proved in this file.

## Origin of the file

Copied unchanged from the Lean library NYLL (https://github.com/n-yamaguchi-0729/NYLL), commit `fe40c03df1b2b195053fdd63305571d97c73ce48`, file `Nyll/ClassFieldTheory/GlobalClassFieldTheory/GlobalClassFields/BigHilbertClassField.lean`: the Lean file is the source byte for byte (SHA-256 `677058e2f396a794fb704ce35b22dbc671dacfc11a9f0f6dc04d936c37c99c75`). That library is distributed under the Apache License, Version 2.0; its licence and notice are kept with the Library's licences.
