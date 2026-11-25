# From a zero norm class to norm membership

Module `Nyll.ClassFieldTheory.GlobalClassFieldTheory.IdealClassFieldTheory.RationalFiniteNormTransfer.ZeroTransport`, copied unchanged from the Lean library NYLL. The origin of the file is given at the end of this page.

This file works in the rational idele class formation. There are closed subgroups L ≤ H ≤ K of Gal(ℚ̄/ℚ), of finite index, each normal in the next. Their fixed fields form a tower B ⊆ E ⊆ U. Let c be an idele class of B. The file turns a statement in the abstract class formation into a concrete one. The abstract statement: c, included into the H-fixed part, has zero finite norm class for L/H. The concrete one: the ordinary extension of c to E lies in the range N(C_U) of the idele-class norm from U to E.

## Main result

`rationalFiniteNormTransferCanonicalFiniteNormClassZero_implies_normMembership`: from the hypothesis `hincludeCanonical : rationalFiniteNormTransferCanonicalFiniteNormClassZero K H L hHK hLH c` it concludes `rationalFiniteNormTransferCanonicalOrdinaryExtensionNormMembership K H L … c`. That is, `ideleClassExtension B E c` lies in the range of the idele-class norm from U to E.

## Proof

A chain of private steps, each stated through the named propositions and `…Data` wrappers of the membership-types file:

1. The isomorphism of finite norm quotients with ordinary norm quotients (`rationalFiniteNormTransferFiniteNormClass_spec`) sends the zero class to the quotient class of the included representative. So that class is 0.
2. A class that is 0 in C_E / N(C_U) lies in the norm range.
3. The included representative equals the ordinary extension of c, by `rationalFiniteNormTransferCanonicalFixedRepresentative_eq_extension`.
4. The membership is moved from the absolute presentation of the middle field to its presentation relative to B.

## Points to watch

- The vanishing of the finite norm class is a hypothesis. This file does not prove it. For the Hilbert-class-field tower of the principal ideal theorem it comes from the Witt-transfer capitulation, in another file.
- Both normality hypotheses (H in K, L in H) are needed, since the extension and the norm map are taken in Galois extensions.

## Origin of the file

Copied unchanged from the Lean library NYLL (https://github.com/n-yamaguchi-0729/NYLL), commit `fe40c03df1b2b195053fdd63305571d97c73ce48`, file `Nyll/ClassFieldTheory/GlobalClassFieldTheory/IdealClassFieldTheory/RationalFiniteNormTransfer/ZeroTransport.lean`: the Lean file is the source byte for byte (SHA-256 `c9bae7c555278dcc14d8ca7cf1efac7bc72c9fb93bb8e27dd2d715ea4544cfdb`). That library is distributed under the Apache License, Version 2.0; its licence and notice are kept with the Library's licences.
