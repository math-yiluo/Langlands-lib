# `Langlands.TauCeti.Algebra.AlgebraicGroup.FunctorOfPoints`

Port of the TauCeti file `TauCeti/Algebra/AlgebraicGroup/FunctorOfPoints.lean` at commit `8428d6217f74afa72531df0bc85d7b57ab72810f`, from the
registered source `tauceti-8428d621-weil-restriction-closure`. Copyright (c) 2026 The Tau Ceti contributors,
released under the Apache 2.0 license; the licence and a notice are in
`licenses/TauCeti/`. The upstream header, module documentation, module-system
keywords (`module`, `public`, `@[expose]`) and declaration names are kept, and no
declaration is renamed.

## Contents

For a Hopf algebra `H` over `R` (not necessarily commutative) and a commutative
`R`-algebra `A`, the convolution monoid `WithConv (H →ₐ[R] A)` (from Mathlib's
`Mathlib.RingTheory.Bialgebra.Convolution`) is a group with inverse `f ↦ f ∘ S`,
`S` the antipode.

- `AlgHom.antipodeComp`, `AlgHom.convInvOfSemiring`, `WithConv.algHom_inv_apply`:
  the inverse `f ↦ f ∘ S` and its value on elements.
- `AlgHom.convGroupOfSemiring`: the group structure; `AlgHom.convCommGroupOfSemiring`:
  commutative when `H` is cocommutative.
- `AlgHom.mapValue φ`: post-composition with `φ : A →ₐ[R] B` as a monoid
  homomorphism of convolution monoids (bialgebra source suffices), with
  `ofConv_comp_mapValue`, `mapValue_id`, `mapValue_comp`, `mapValue_injective`,
  `mem_mrange_mapValue_iff`, and `WithConv.mapValue_algebraOfId`.

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
