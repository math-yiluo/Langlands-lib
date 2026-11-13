# Local relative Weil maps on a prime-transported completion package

Author: Worker 5093. This is a supporting unit for task
`92a3d086-a5ad-476f-9fd9-aa9d4eaa3778`, which must prove
`Langlands.LocalFactor.NonabelianBrauer.KernelCompatibilityStatement`. At the distinguished place of
the global argument, the completion `𝕃_u` of a global generator field is used through the package
`towerPadicField v u = padicFieldAt u (residuePrime_eq v u)`, whose prime index is the residue
prime of the place `v` below. The published existence statement for local relative Weil maps is
stated for the canonical package `padicField u`. This unit restates its consequence for
`padicFieldAt u h`, for any `h : residuePrime u = p`. It is bookkeeping with no separate literature
source.

Everything is in `Langlands.LocalFactor.NonabelianBrauer`.

## Result

`exists_localMap_padicFieldAt`: assume

- `hM : LocalRelativeWeilMapExistenceStatement.{0}` (Tate 1979, (1.6.1): existence of local maps
  into relative Weil groups for arithmetic fundamental classes),
- `hN3 : LocalTransferReciprocityStatement.{0}` (the transfer of a local map is inverse geometric
  local reciprocity),
- an invariant family `I` with the relative class formation and arithmetic normalization properties,
  and a class family `c` that generates, restricts, inflates and is locally compatible with `I`
  (the hypotheses of `hM`),
- a Galois extension `K' / 𝕃` of number fields in `Type`, a finite place `u` of `𝕃`, a place `w` of
  `K'` above it, and a geometric reciprocity candidate `ew` of `K'_w` (`towerPadicField u w`).

Then for every `h : residuePrime u = p` there is a function
`ι : W(padicFieldAt u h) → W_{K'/𝕃}` such that

1. for `g ∈ W(padicFieldAt u h)` and `x ∈ K'`, the projection of `ι g` acts on `x` as `g` acts
   through `completionClosureEmbedding u w : K'_w → \bar{𝕃_u}`;
2. for every geometric candidate `ez` of `padicFieldAt u h`, the transfer of `ι y` to `C_𝕃` is the
   inverse of the image of `rec_{ez} y` under `𝕃_u^× → C_𝕃`.

Proof: substitute `h`; then `padicFieldAt u rfl` is definitionally `padicField u`. `hM` gives a local
relative Weil map `ι` for `ew`; clause 2 of `IsLocalRelativeWeilMap` is item 1 and `hN3` gives
item 2.
