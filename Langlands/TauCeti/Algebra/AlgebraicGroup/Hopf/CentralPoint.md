# `Langlands.TauCeti.Algebra.AlgebraicGroup.Hopf.CentralPoint`

Port of the TauCeti file `TauCeti/Algebra/AlgebraicGroup/Hopf/CentralPoint.lean` at commit `8428d6217f74afa72531df0bc85d7b57ab72810f`, from the
registered source `tauceti-8428d621-weil-restriction-closure`. Copyright (c) 2026 The Tau Ceti contributors,
released under the Apache 2.0 license; the licence and a notice are in
`licenses/TauCeti/`. The upstream header, module documentation, module-system
keywords (`module`, `public`, `@[expose]`) and declaration names are kept, and no
declaration is renamed.

## Contents

Central points of the functor of points `A ↦ (H →ₐ[R] A)` of a bialgebra `H`.

- `TauCeti.HopfAlgebra.IsCentralPoint g`: the image of `g` in every `G(B)`, `B` an
  `A`-algebra, commutes with every point of `G(B)`; basic API (`commute`,
  `mapValue`, `mapDomain_bialgEquiv`, `isCentralPoint_one`, `mul`, `inv`,
  `isCentralPoint_of_isCocomm`).
- `TauCeti.HopfAlgebra.center`: the central points as a subgroup (Hopf case), with
  `instIsMulCommutativeCenter` and `center_le_center`.
- `isCentralPoint_iff_commute_includeRight`: one test algebra `A ⊗[R] H` suffices;
  `commute_includeLeft_includeRight_iff_isCocomm`,
  `convMul_includeRight_includeLeft` and `isCentralPoint_id_iff_isCocomm`.

In this closure it is a private import of `Algebra/HopfAlgebra/WeilRestriction`.

## Edits relative to upstream

- Imports renamed from `TauCeti.*` to `Langlands.TauCeti.*`: `Langlands.TauCeti.Algebra.AlgebraicGroup.Hopf.Map`, `Langlands.TauCeti.Algebra.Coalgebra.Convolution`.

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
