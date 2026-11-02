# `Langlands.TauCeti.Algebra.Polynomial.Laurent.Polynomial`

Port of the TauCeti file `TauCeti/Algebra/Polynomial/Laurent/Polynomial.lean` at commit `8428d6217f74afa72531df0bc85d7b57ab72810f`, from the
registered source `tauceti-8428d621-weil-restriction-closure`. Copyright (c) 2026 The Tau Ceti contributors,
released under the Apache 2.0 license; the licence and a notice are in
`licenses/TauCeti/`. The upstream header, module documentation, module-system
keywords (`module`, `public`, `@[expose]`) and declaration names are kept, and no
declaration is renamed.

## Contents

Laurent polynomials coming from polynomials.

- `TauCeti.exists_toLaurent_eq_iff`: a Laurent polynomial is in the image of
  `Polynomial.toLaurent` exactly when its negative coefficients vanish.
- `TauCeti.exists_algHom_toLaurent_comp_eq_iff`: the same criterion for an algebra
  homomorphism with Laurent-polynomial values.
- `LaurentPolynomial.isScalarTower_polynomial`: the scalar tower
  `R → R[X] → R[T;T⁻¹]`.

## Edits relative to upstream

- None: apart from the added port note comment, the Lean text is byte-identical
  to the upstream file (it has no TauCeti-internal imports).

## Port note

The Lean file carries a port note comment between the upstream copyright
header and the `module` keyword. It names the upstream file, the commit, the
repository `https://github.com/TauCetiProject/TauCeti` and the registered
source, and lists the edits above.

## Credit

Port prepared from Worker 207's shared draft for task 46249db5 (the import
renaming, the compatibility fixes and this description), with the port note and
licence files added by Worker 1122. It builds with lake against environment
`3b864ddf-f0af-4c18-8903-c6f813a0ce0f` over Library commit
`dad4d948ab2f6838277ce9094bcc92df1507b0cb` with 0 errors and 0 warnings.
