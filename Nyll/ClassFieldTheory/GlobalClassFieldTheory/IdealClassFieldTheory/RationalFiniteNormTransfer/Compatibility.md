# Fixed-field inclusion is extension of idele classes

Module `Nyll.ClassFieldTheory.GlobalClassFieldTheory.IdealClassFieldTheory.RationalFiniteNormTransfer.Compatibility`, copied unchanged from the Lean library NYLL. The origin of the file is given at the end of this page.

This file works in the rational idele class formation. There are closed subgroups L ≤ K of Gal(ℚ̄/ℚ), of finite index, with L normal in K, and with fixed fields F and E. Let c be an idele class of F. The file shows that including c from the K-fixed part into the L-fixed part of the idele-class module gives its ordinary extension to E. That extension is the image of c under the idele-class extension map C_F → C_E.

## Main definitions and results

The file names three propositions about c and proves each:

- `rationalFiniteNormTransferCanonicalBaseChangeCompatibility`: the abstract extension endpoint of c equals its ordinary extension representative in C_E. It is proved by `..._proof`.
- `rationalFiniteNormTransferCanonicalToOrdinaryCompatibility`: the same endpoint equals the canonical fixed-field representative of c, read back as an idele class of E. It is proved by `..._proof`.
- `rationalFiniteNormTransferCanonicalFixedRepresentativeExtensionCompatibility`: the fixed-field representative equals the ordinary extension. It is proved by `rationalFiniteNormTransferCanonicalFixedRepresentative_eq_extension`, which combines the first two.

## Proof

The first proposition is reduced to the imported fact `rationalFixedFieldInclusion_baseChange_eq_ideleClassExtension`. To apply it, c is written as the base change of a relative idele class of F over ℚ. The second proposition follows from `rationalAbstractExtensionIdeleClassEquiv_to_ordinary`, which compares the two identifications of the L-fixed part with C_E.

## Points to watch

The results are stated through named propositions (`def … : Prop`), not as equations in the theorem types. They are bridge lemmas for the norm-transfer step of the principal ideal theorem.

## Origin of the file

Copied unchanged from the Lean library NYLL (https://github.com/n-yamaguchi-0729/NYLL), commit `fe40c03df1b2b195053fdd63305571d97c73ce48`, file `Nyll/ClassFieldTheory/GlobalClassFieldTheory/IdealClassFieldTheory/RationalFiniteNormTransfer/Compatibility.lean`: the Lean file is the source byte for byte (SHA-256 `9c04e507847bb7384644fa9723a3e178d34c2a0bece6c941ff94d42c52db1f0a`). That library is distributed under the Apache License, Version 2.0; its licence and notice are kept with the Library's licences.
