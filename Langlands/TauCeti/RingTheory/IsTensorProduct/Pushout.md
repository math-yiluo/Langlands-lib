# `Langlands.TauCeti.RingTheory.IsTensorProduct.Pushout`

Port of the TauCeti file `TauCeti/RingTheory/IsTensorProduct/Pushout.lean` at commit `8428d6217f74afa72531df0bc85d7b57ab72810f`, from the
registered source `tauceti-8428d621-weil-restriction-closure`. Copyright (c) 2026 The Tau Ceti contributors,
released under the Apache 2.0 license; the licence and a notice are in
`licenses/TauCeti/`. The upstream header, module documentation, module-system
keywords (`module`, `public`, `@[expose]`) and declaration names are kept, and no
declaration is renamed.

## Contents

Homomorphisms and ideals under `Algebra.IsPushout R S R' S'`.

- `Algebra.IsPushout.lift`, `lift_algebraMap`, `algHom_ext'`: `R'`-algebra maps out
  of `S'`; `Algebra.IsPushout.liftRingHom`, `ringHom_ext`: ring maps out of `S'`.
- `Ideal.restrictScalars_map_eq_span`.
- `Module.Finite.of_isPushout`, `Module.Projective.of_isPushout`,
  `Algebra.FinitePresentation.of_isPushout`.
- `Algebra.IsPushout.cancelBaseChangeAlg_symm_lTensor`: naturality of
  `S ⊗[R] T ≃ₐ[S] S' ⊗[R'] T` in `T`.

## Edits relative to upstream

- Imports renamed from `TauCeti.*` to `Langlands.TauCeti.*`: `Langlands.TauCeti.RingTheory.TensorProduct.Maps`.

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
