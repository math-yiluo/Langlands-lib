# Fixed fields of closed subgroups of Gal(ℚ̄/ℚ) as number fields

Module `Nyll.ClassFieldTheory.GlobalClassFieldTheory.IdealClassFieldTheory.RationalFiniteNormTransfer.FieldSpine`, copied unchanged from the Lean library NYLL. The origin of the file is given at the end of this page.

The rational finite-norm transfer files work with closed subgroups L ≤ K of Gal(ℚ̄/ℚ), where ℚ̄ is `SeparableClosure ℚ`. K has finite index in the whole group, and L has finite index in K. Let F and E be their fixed fields. This file supplies once and for all the structures these files need on F and E. It also names the types the transfer acts on.

## Main definitions and results

In the namespace `RationalFiniteNormTransferInternal`:

- `fixedFiniteDimensional`, `fixedNumberField`: F is finite over ℚ and a number field.
- `relativeFiniteDimensional`, `relativeScalarTower`, `relativeAbsoluteFiniteDimensional`, `relativeNumberField`: E is finite over F, ℚ → F → E is a scalar tower, and E is finite over ℚ and a number field.
- `relativeIsGalois`: if L is normal in K, then E/F is Galois.
- `absoluteFinite`: L has finite index in the whole group.
- `ideleClassGroupIsMulCommutative`, `ideleClassSubgroupNormal`: idele class groups are commutative, and all their subgroups are normal.
- `absoluteAlgebra` names the ℚ-algebra structure on E. `quotientTargetZero` names the zero of the quotient type below.

Named types:

- `rationalFiniteNormTransferBaseIdeleClass K`: the idele class group C_F.
- `rationalFiniteNormTransferQuotientTarget K L hLK hnormal`: the quotient of C_F by the range of the idele-class norm from E, written additively.
- `rationalFiniteNormTransferExtensionIdeleClass K L hLK`: the idele class group C_E.

## Points to watch

- The structural facts are stated as theorems, not as global instances. Other files install them with `letI` or as local instances. This keeps one fixed instance path for these dependent types.
- The fields are fixed fields inside `SeparableClosure ℚ`, not arbitrary number fields. The finiteness assumptions are instance arguments on quotients of closed subgroups.

## Origin of the file

Copied unchanged from the Lean library NYLL (https://github.com/n-yamaguchi-0729/NYLL), commit `fe40c03df1b2b195053fdd63305571d97c73ce48`, file `Nyll/ClassFieldTheory/GlobalClassFieldTheory/IdealClassFieldTheory/RationalFiniteNormTransfer/FieldSpine.lean`: the Lean file is the source byte for byte (SHA-256 `a6baf27b82947e8ec68ba6973bf280d274eaa542f0e2082361f38601d558f42c`). That library is distributed under the Apache License, Version 2.0; its licence and notice are kept with the Library's licences.
