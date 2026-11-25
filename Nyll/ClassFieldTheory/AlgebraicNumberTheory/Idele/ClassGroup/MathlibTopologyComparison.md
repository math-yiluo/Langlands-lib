# The comparison with Mathlib's idele class group is a homeomorphism

Module `Nyll.ClassFieldTheory.AlgebraicNumberTheory.Idele.ClassGroup.MathlibTopologyComparison`, copied unchanged from the Lean library NYLL. The origin of the file is given at the end of this page.

For a number field `K`, the file upgrades the algebraic isomorphism `ideleClassGroupEquivMathlib` between the library's restricted-product idele class group and Mathlib's `NumberField.IdeleClassGroup (𝓞 K) K` (the quotient of the units of the adele ring) to an isomorphism of topological groups.

- `continuous_ideleClassGroupEquivMathlib`: the forward map is continuous.
- `ideleClassGroupContinuousMulEquivMathlib`: the isomorphism of topological groups `IdeleClassGroup K ≃ₜ* NumberField.IdeleClassGroup (𝓞 K) K`.

Both directions are obtained by descending through the quotient maps the continuity of the imported isomorphism of topological groups between the two idele groups (`continuous_equivAdeleRingUnits`, `equivAdeleRingUnitsContinuousMulEquiv`).

## Origin of the file

Copied unchanged from the Lean library NYLL (https://github.com/n-yamaguchi-0729/NYLL), commit `fe40c03df1b2b195053fdd63305571d97c73ce48`, file `Nyll/ClassFieldTheory/AlgebraicNumberTheory/Idele/ClassGroup/MathlibTopologyComparison.lean`: the Lean file is the source byte for byte (SHA-256 `e062a9eb7043dc94df73922e3d6fa36c56f5e5f53940b108be279537445e69a3`). That library is distributed under the Apache License, Version 2.0; its licence and notice are kept with the Library's licences.
