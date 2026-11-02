# `Langlands.TauCeti.Algebra.AlgebraicGroup.Hopf.Map`

Port of the TauCeti file `TauCeti/Algebra/AlgebraicGroup/Hopf/Map.lean` at commit `8428d6217f74afa72531df0bc85d7b57ab72810f`, from the
registered source `tauceti-8428d621-weil-restriction-closure`. Copyright (c) 2026 The Tau Ceti contributors,
released under the Apache 2.0 license; the licence and a notice are in
`licenses/TauCeti/`. The upstream header, module documentation, module-system
keywords (`module`, `public`, `@[expose]`) and declaration names are kept, and no
declaration is renamed.

## Contents

Contravariant functoriality of points in the coordinate bialgebra.

- `BialgHom.mapDomain φ`: pre-composition by a bialgebra morphism
  `φ : H₁ →ₐc[R] H₂` as a monoid homomorphism
  `WithConv (H₂ →ₐ[R] A) →* WithConv (H₁ →ₐ[R] A)`, with `mapDomain_apply`,
  `mapDomain_apply_apply`, `mapDomain_injective_of_surjective`, `mapDomain_id`,
  `mapDomain_comp`.
- `BialgEquiv.mapDomainMulEquiv`: the multiplicative-equivalence version for a
  bialgebra isomorphism.
- `BialgHom.mapValue_mapDomain`: pre- and post-composition commute;
  `BialgHom.mapDomain_inv_apply`: the inverse after pre-composition.

## Edits relative to upstream

- Imports renamed from `TauCeti.*` to `Langlands.TauCeti.*`: `Langlands.TauCeti.Algebra.AlgebraicGroup.FunctorOfPoints`.

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
