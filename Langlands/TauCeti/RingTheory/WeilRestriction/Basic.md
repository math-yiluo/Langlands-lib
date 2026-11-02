# `Langlands.TauCeti.RingTheory.WeilRestriction.Basic`

Port of the TauCeti file `TauCeti/RingTheory/WeilRestriction/Basic.lean` at commit `8428d6217f74afa72531df0bc85d7b57ab72810f`, from the
registered source `tauceti-8428d621-weil-restriction-closure`. Copyright (c) 2026 The Tau Ceti contributors,
released under the Apache 2.0 license; the licence and a notice are in
`licenses/TauCeti/`. The upstream header, module documentation, module-system
keywords (`module`, `public`, `@[expose]`) and declaration names are kept, and no
declaration is renamed.

## Contents

Weil restriction along a finite projective algebra. Here `B` is an `A`-algebra
that is finite and projective as an `A`-module and `C` a `B`-algebra of finite
presentation.

- `TauCeti.Algebra.WeilRestriction A B C`: an `A`-algebra of finite presentation
  (`instFinitePresentation`) representing `T ↦ (C →ₐ[B] B ⊗[A] T)`, with
  `universalPoint`, the bijection `homEquiv A B C T`, its naturality
  `homEquiv_comp` and `hom_ext`.
- `WeilRestriction.map`, `homEquiv_comp_map`, `map_surjective`,
  `range_le_iff_range_homEquiv_le`.
- `WeilRestriction.baseChangeAlgEquiv`: for pushouts `B' = B ⊗[A] A'`,
  `C' = C ⊗[B] B'`, the isomorphism
  `A' ⊗[A] WeilRestriction A B C ≃ₐ[A'] WeilRestriction A' B' C'`, with
  `homEquiv_comp_baseChangeAlgEquiv`.
- `WeilRestriction.tensorHomEquiv`, `tensorHomEquiv_comp`.

## Edits relative to upstream

- Imports renamed from `TauCeti.*` to `Langlands.TauCeti.*`: `Langlands.TauCeti.RingTheory.IsTensorProduct.Pushout`, `Langlands.TauCeti.RingTheory.Extension.Presentation.Basic`.

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
