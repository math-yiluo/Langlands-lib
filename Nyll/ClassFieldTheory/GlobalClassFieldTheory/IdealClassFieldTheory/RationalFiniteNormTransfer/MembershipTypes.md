# Named norm-membership statements for the rational norm transfer

Module `Nyll.ClassFieldTheory.GlobalClassFieldTheory.IdealClassFieldTheory.RationalFiniteNormTransfer.MembershipTypes`, copied unchanged from the Lean library NYLL. The origin of the file is given at the end of this page.

This file works in the rational idele class formation, with closed subgroups L ≤ H ≤ K of Gal(ℚ̄/ℚ) of finite index, L normal in H (argument `hLHnormal`). The statements on the ordinary extension of c also take H normal in K (`hHKnormal`). Their fixed fields form a tower B ⊆ E ⊆ U. The norm-transfer argument for the principal ideal theorem must show that an idele class c of B, once extended to E, is a norm from U. This file names the propositions that occur along the way, and wrappers for them. It proves nothing.

## Main definitions

All of the following are propositions (`def … : Prop`):

- `rationalFiniteNormTransferRelativeNormMembership`: an idele class of E lies in the range of the idele-class norm from U. Here E is presented as a relative fixed field over B.
- `rationalFiniteNormTransferCanonicalOrdinaryExtensionNormMembership`: marked `@[irreducible]`. It is the previous statement for the ordinary extension of c from B to E.
- `rationalFiniteNormTransferCanonicalOrdinaryExtensionAbsoluteNormMembership`: the same membership, with the middle field presented as the absolute fixed field of H.
- `rationalFiniteNormTransferCanonicalFiniteNormRepresentativeAbsoluteNormMembership`: membership in the norm range of a different representative. It is obtained by including c into the H-fixed part of the idele-class module and reading it back as an idele class.
- `…FiniteNormRepresentativeQuotientZero`: the norm-quotient class of that representative equals the image of 0 under `rationalFiniteNormQuotientEquivIdeleClassNormQuotient`.
- `…FiniteNormRepresentativeTargetZero`: that class is 0 in `rationalFiniteNormTransferQuotientTarget`.

For several of these propositions, a one-field structure with the suffix `Data` (for instance `RationalFiniteNormTransferCanonicalNormMembershipData`) packages a proof as a `Type`.

## Points to watch

- The file contains only definitions. Which of the propositions hold, and how they imply one another, is shown in other files.
- The relative and absolute presentations describe the same middle field with different instance paths. The file keeps them as separate statements on purpose.

## Origin of the file

Copied unchanged from the Lean library NYLL (https://github.com/n-yamaguchi-0729/NYLL), commit `fe40c03df1b2b195053fdd63305571d97c73ce48`, file `Nyll/ClassFieldTheory/GlobalClassFieldTheory/IdealClassFieldTheory/RationalFiniteNormTransfer/MembershipTypes.lean`: the Lean file is the source byte for byte (SHA-256 `46bf97f782f139245c02950b457862a6037c1e4183a90cf90a3bbc7671417e40`). That library is distributed under the Apache License, Version 2.0; its licence and notice are kept with the Library's licences.
