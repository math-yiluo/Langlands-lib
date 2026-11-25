# Abstract extension and ordinary idele classes over ℚ

Module `Nyll.ClassFieldTheory.GlobalClassFieldTheory.IdealClassFieldTheory.RationalAbstractExtensionToOrdinary`, copied unchanged from the Lean library NYLL. The origin of the file is given at the end of this page.

In the rational idele class formation, finite extensions are closed subgroups L ≤ K of Gal(ℚ̄/ℚ) with L normal in K and of finite index. K itself is assumed of finite index in Gal(ℚ̄/ℚ) (instance `hKfinite`). The fixed fields F (of K) and E (of L) are then number fields. The file compares two ways of turning an element x of the L-fixed part of the idele-class module into an idele class of E.

## Main result

`rationalAbstractExtensionIdeleClassEquiv_to_ordinary`: these two routes agree.
- First route: apply the abstract extension isomorphism `rationalAbstractExtensionIdeleClassEquiv`, then the comparison `relativeIdeleClassBaseChangeMulEquiv` from relative idele classes of E/F to C_E.
- Second route: apply `extensionFixedRepresentationEquiv`, then the inverse of the fixed-field isomorphism between C_E and the L-fixed part of the ambient module.

Both routes give the same element of C_E.

## Proof

The proof unfolds both sides to relative idele classes of E over ℚ. It concludes with the tower compatibility of relative-idele base change for ℚ ⊆ F ⊆ E (`relativeIdeleClassBaseChangeMulEquiv_tower`).

## Points to watch

The statement is internal plumbing between the abstract class-formation model over ℚ and concrete idele class groups. Finiteness and normality enter as instance and explicit arguments on closed subgroups, not as hypotheses on fields.

## Origin of the file

Copied unchanged from the Lean library NYLL (https://github.com/n-yamaguchi-0729/NYLL), commit `fe40c03df1b2b195053fdd63305571d97c73ce48`, file `Nyll/ClassFieldTheory/GlobalClassFieldTheory/IdealClassFieldTheory/RationalAbstractExtensionToOrdinary.lean`: the Lean file is the source byte for byte (SHA-256 `cdf9337be964a70855411a5014b09cac56c03c3b8374628b42940d23835ef5f1`). That library is distributed under the Apache License, Version 2.0; its licence and notice are kept with the Library's licences.
