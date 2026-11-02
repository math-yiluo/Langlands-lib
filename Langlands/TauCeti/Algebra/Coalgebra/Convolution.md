# `Langlands.TauCeti.Algebra.Coalgebra.Convolution`

Port of the TauCeti file `TauCeti/Algebra/Coalgebra/Convolution.lean` at commit `8428d6217f74afa72531df0bc85d7b57ab72810f`, from the
registered source `tauceti-8428d621-weil-restriction-closure`. Copyright (c) 2026 The Tau Ceti contributors,
released under the Apache 2.0 license; the licence and a notice are in
`licenses/TauCeti/`. The upstream header, module documentation, module-system
keywords (`module`, `public`, `@[expose]`) and declaration names are kept, and no
declaration is renamed.

## Contents

Convolution identities used by the Hopf structure on the Weil restriction.

- `TauCeti.Coalgebra.comul_eq_convMul_includeLeft_includeRight`: `Δ` is the
  convolution product of the two tensor inclusions.
- `TauCeti.Bialgebra.toConv_comp_comulAlgHom`, `TauCeti.Bialgebra.comulPoint_eq_include_mul`:
  the corresponding identities for algebra-hom points of a bialgebra.
- `WithConv.mulTensor`: the exterior convolution product of linear maps out of `M`
  and `N`, with `mulTensor_apply_tmul`, zero/add/smul rules and `mulTensor_convMul`;
  `AlgHom.toConv_toLinearMap_comp_mul'`.
- `Module.Basis.convCoordEquiv`, with `convCoordEquiv_apply` and
  `convCoordEquiv_symm_apply`: coordinates of convolution-algebra elements in a
  basis of the coefficients.
- `LinearMap.convMul_apply_mem_mul`, `LinearMap.convPow_apply_mem_pow`:
  ideal-valued maps.

**Deviation.** The upstream theorem `Module.Basis.convCoordEquiv_convPostcomp_mul`
(upstream lines 324-337) is deleted: it does not compile against the pinned Mathlib
(`AlgHom.convPostcomp` is unavailable) and nothing in the closure uses it. The
unchanged upstream module documentation still names it.

## Edits relative to upstream

- The theorem `Module.Basis.convCoordEquiv_convPostcomp_mul` (upstream lines 324-337, with its docstring) is deleted.

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
