# Fixed-field inclusion and idele-class extension after base change

Module `Nyll.ClassFieldTheory.GlobalClassFieldTheory.IdealClassFieldTheory.RationalFixedFieldBaseChange`, copied unchanged from the Lean library NYLL. The origin of the file is given at the end of this page.

This file works in the rational idele class formation. There are closed subgroups L ≤ K of Gal(ℚ̄/ℚ), of finite index, with L normal in K. Their fixed fields F ⊆ E are number fields. Start from a relative idele class c of F over ℚ, and let q ∈ C_F be its image under the base-change comparison. The file shows that the abstract inclusion of q into the L-fixed part, read back as an idele class of E, is the ordinary extension of q.

## Main result

`rationalFixedFieldInclusion_baseChange_eq_ideleClassExtension`: the left side does the following to q.
1. Include it, through `rationalAbstractFixedFieldIdeleClassEquivFixed K` and `fixedFieldInclusion`, into the L-fixed part of the idele-class module.
2. Apply the inverse of `extensionFixedRepresentationEquiv`, then the abstract extension isomorphism `rationalAbstractExtensionIdeleClassEquiv`.
3. Compare with C_E by `relativeIdeleClassBaseChangeMulEquiv` for E/F.

The result equals `ideleClassExtension F E q`, written additively.

## Proof

An imported lemma, `rationalAbstractExtensionIdeleClassEquiv_fixedFieldInclusion`, identifies the abstract side with the inclusion of relative idele classes, `RelativeIdeleGroup.classInclusion F E q`. The lemma `relativeIdeleClassBaseChangeMulEquiv_classInclusion` then identifies that inclusion, after base change, with the ordinary extension map.

## Points to watch

The input is written as the base change of a relative idele class over ℚ. Since that comparison is an isomorphism (`MulEquiv`), every element of C_F arises this way. The statement is a bridge lemma between the abstract class formation over ℚ and concrete idele classes.

## Origin of the file

Copied unchanged from the Lean library NYLL (https://github.com/n-yamaguchi-0729/NYLL), commit `fe40c03df1b2b195053fdd63305571d97c73ce48`, file `Nyll/ClassFieldTheory/GlobalClassFieldTheory/IdealClassFieldTheory/RationalFixedFieldBaseChange.lean`: the Lean file is the source byte for byte (SHA-256 `8ec2dc1d9a5e28ed18e2fd57a3f698b449d4a41e208a987000d887bd7731b493`). That library is distributed under the Apache License, Version 2.0; its licence and notice are kept with the Library's licences.
