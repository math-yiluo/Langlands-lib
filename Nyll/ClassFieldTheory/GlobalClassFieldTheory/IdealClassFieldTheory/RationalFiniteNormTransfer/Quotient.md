# Norm quotient maps for the rational norm transfer

Module `Nyll.ClassFieldTheory.GlobalClassFieldTheory.IdealClassFieldTheory.RationalFiniteNormTransfer.Quotient`, copied unchanged from the Lean library NYLL. The origin of the file is given at the end of this page.

This file works in the rational idele class formation, with closed subgroups L ≤ K of Gal(ℚ̄/ℚ) of finite index, L normal in K, and fixed fields F ⊆ E. The file defines the quotient map of C_F onto the ordinary norm quotient C_F / N(C_E), where N is the idele-class norm from E to F. It shows that the comparison isomorphism sends each abstract finite norm class of the class formation to the image under this map of its ordinary idele-class representative.

## Main definitions and results

- `rationalFiniteNormTransferQuotientMap K L hLK hnormal`: the quotient map C_F → C_F / N(C_E), written additively.
- `rationalFiniteNormTransferNormMembership K L hLK hnormal c`: the proposition that c ∈ C_F lies in N(C_E).
- `rationalFiniteNormTransferFiniteNormClass_spec`: let b be an element of the K-fixed part of the idele-class module. The isomorphism `rationalFiniteNormQuotientEquivIdeleClassNormQuotient` sends the abstract finite norm class of b to the quotient class of the idele class of F that corresponds to b. The proof cites the imported lemma `rationalFiniteNormQuotientEquivIdeleClassNormQuotient_finiteNormClass`.
- `rationalFiniteNormTransferCanonicalFiniteNormClassZero K H L hHK hLH c`: for a tower L ≤ H ≤ K, the proposition that c ∈ C_F, included into the H-fixed part, has zero finite norm class for L/H.

## Points to watch

The last definition is a proposition, not a theorem. Where it holds is shown elsewhere, for the tower used in the principal ideal theorem.

## Origin of the file

Copied unchanged from the Lean library NYLL (https://github.com/n-yamaguchi-0729/NYLL), commit `fe40c03df1b2b195053fdd63305571d97c73ce48`, file `Nyll/ClassFieldTheory/GlobalClassFieldTheory/IdealClassFieldTheory/RationalFiniteNormTransfer/Quotient.lean`: the Lean file is the source byte for byte (SHA-256 `9ebe11c7b9c08b338a0fc7ba171339eb4bc0e0e1c1876ab4b91e49868f608013`). That library is distributed under the Apache License, Version 2.0; its licence and notice are kept with the Library's licences.
