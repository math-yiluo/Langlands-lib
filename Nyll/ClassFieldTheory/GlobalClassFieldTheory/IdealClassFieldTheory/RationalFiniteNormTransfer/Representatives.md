# Representatives of extended idele classes in the rational transfer

Module `Nyll.ClassFieldTheory.GlobalClassFieldTheory.IdealClassFieldTheory.RationalFiniteNormTransfer.Representatives`, copied unchanged from the Lean library NYLL. The origin of the file is given at the end of this page.

This file works in the rational idele class formation, with closed subgroups L ≤ K of Gal(ℚ̄/ℚ) of finite index and fixed fields F ⊆ E. An idele class of F can be pushed up to an idele class of E in several ways. The file names each of them, so that other files can compare them.

## Main definitions

- `rationalFiniteNormTransferAbstractRepresentative K L hLK a`: let a be an element of the K-fixed part of the idele-class module. Include it into the L-fixed part and read it back as an idele class of E, with E presented as the absolute fixed field of L.
- `rationalFiniteNormTransferCanonicalFixedRepresentative K L hLK c`: for c ∈ C_F, the same inclusion, read back through the presentation of E as a relative fixed field over F.
- `rationalFiniteNormTransferOrdinaryExtensionRepresentative K L hLK hnormal c`: the ordinary extension of c, `ideleClassExtension F E c`.
- `rationalFiniteNormTransferCanonicalAbstractExtensionEndpoint K L hLK hnormal c`: the class obtained from the included element through the abstract extension isomorphism `rationalAbstractExtensionIdeleClassEquiv`, followed by the comparison of relative and ordinary idele classes of E. It is written additively.

## Points to watch

The file contains only definitions. It proves no equality between these representatives; the comparisons are proved in other files. Normality of L in K is an argument only where a Galois structure on E/F is needed.

## Origin of the file

Copied unchanged from the Lean library NYLL (https://github.com/n-yamaguchi-0729/NYLL), commit `fe40c03df1b2b195053fdd63305571d97c73ce48`, file `Nyll/ClassFieldTheory/GlobalClassFieldTheory/IdealClassFieldTheory/RationalFiniteNormTransfer/Representatives.lean`: the Lean file is the source byte for byte (SHA-256 `782bd49707b30ad6185276b1239a62e33ec6d825c54610b9816deaa955a66ef4`). That library is distributed under the Apache License, Version 2.0; its licence and notice are kept with the Library's licences.
