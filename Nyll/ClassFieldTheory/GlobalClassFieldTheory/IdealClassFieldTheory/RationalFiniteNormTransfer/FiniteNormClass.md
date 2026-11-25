# Norm classes after inclusion of fixed fields

Module `Nyll.ClassFieldTheory.GlobalClassFieldTheory.IdealClassFieldTheory.RationalFiniteNormTransfer.FiniteNormClass`, copied unchanged from the Lean library NYLL. The origin of the file is given at the end of this page.

This file works in the rational idele class formation. There are closed subgroups L ≤ H ≤ K of Gal(ℚ̄/ℚ), of finite index, with L normal in H. Let a be an element of the K-fixed part of the idele-class module. The file computes, in an ordinary norm quotient of idele classes, the norm class of a for the extension L/H after including a into the H-fixed part.

## Main result

`rationalFiniteNormTransferFiniteNormClass_eq_abstractRepresentative` concerns the finite norm class of `fixedFieldInclusion K H hHK a` for L/H. The isomorphism `rationalFiniteNormQuotientEquivIdeleClassNormQuotient` sends this class to an ordinary norm quotient of idele classes. The result is the quotient class of the named representative `rationalFiniteNormTransferAbstractRepresentative K H hHK a`.

## Proof

It is the specification lemma `rationalFiniteNormTransferFiniteNormClass_spec`, applied to the included element.

## Points to watch

This is a bridge lemma for the norm-transfer argument in the principal ideal theorem. It concerns idele classes of the fixed fields of H and L, which are number fields, not ideals.

## Origin of the file

Copied unchanged from the Lean library NYLL (https://github.com/n-yamaguchi-0729/NYLL), commit `fe40c03df1b2b195053fdd63305571d97c73ce48`, file `Nyll/ClassFieldTheory/GlobalClassFieldTheory/IdealClassFieldTheory/RationalFiniteNormTransfer/FiniteNormClass.lean`: the Lean file is the source byte for byte (SHA-256 `d6f3cd739116802c9895da983fe533615f9b439bfdc3a7aa54b5219532ef2435`). That library is distributed under the Apache License, Version 2.0; its licence and notice are kept with the Library's licences.
