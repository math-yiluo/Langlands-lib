# Comparison with Mathlib's idele class group

Module `Nyll.ClassFieldTheory.AlgebraicNumberTheory.Idele.ClassGroup.MathlibComparison`, copied unchanged from the Lean library NYLL. The origin of the file is given at the end of this page.

The library's idele group of a number field `K` is a restricted product; Mathlib's `NumberField.IdeleGroup (𝓞 K) K` is the unit group of the adele ring. The imported group isomorphism `equivAdeleRingUnits` between them matches the principal subgroups, so it descends to idele class groups.

- `equivAdeleRingUnits_principalIdele`: the principal idele of `x ∈ Kˣ` goes to Mathlib's diagonal idele `unitEmbedding (𝓞 K) K x`.
- `ideleClassGroupEquivMathlib`: the induced group isomorphism `IdeleClassGroup K ≃* NumberField.IdeleClassGroup (𝓞 K) K`.
- `equivAdeleRingUnits_finitePlaceIdele` and `ideleClassGroupEquivMathlib_finitePlaceIdeleClass`: the idele (or idele class) concentrated at one finite place `v`, with component `x ∈ K_vˣ`, corresponds to Mathlib's `ofAdicCompletion (𝓞 K) K v x`. The file comment says this comparison is needed for the public statement of local–global reciprocity.

The isomorphism here is algebraic only; its continuity is not treated in this file.

## Origin of the file

Copied unchanged from the Lean library NYLL (https://github.com/n-yamaguchi-0729/NYLL), commit `fe40c03df1b2b195053fdd63305571d97c73ce48`, file `Nyll/ClassFieldTheory/AlgebraicNumberTheory/Idele/ClassGroup/MathlibComparison.lean`: the Lean file is the source byte for byte (SHA-256 `35dd721495ee367a399e6dee9c9338676cb624d28d929dd69a9665a4d4d2e552`). That library is distributed under the Apache License, Version 2.0; its licence and notice are kept with the Library's licences.
