# The level-zero type of a cuspidal datum on the unit group of a standard order

Module `Langlands.BushnellKutzko.SplitTypeJacquet.StandardType`. Let `F` be a nonarchimedean
local field, `n = m + 1`, and `E` a Harish–Chandra datum over the residue field `k_F` with block
shape `B`.

- `redJ0 B : J0 F (blkOf B) →* B.parabolic k_F` is reduction, and `stdType E` is the
  representation of `J0 F (blkOf B)` on `E.leviRep` obtained by inflating the Levi tensor of `E`
  through `redJ0` and the Levi projection. It is trivial on `J1 F (blkOf B)`
  (`stdType_eq_one_of_mem_J1`).
- `isIrreducible_parabolicRep`: the inflated Levi tensor is an irreducible representation of the
  parabolic. The Levi tensor is irreducible (`FiniteRep.isIrreducible_externalRep`), and
  subrepresentations of a pullback along a surjective homomorphism correspond to those of the
  original representation (`subrepCompOrderIso`).
- `upperC_apply` computes the entries of the corner element `upperC blk j Z`. For an integral
  corner it lies in `GL_n(𝔬_F)` (`upperC_mem_Kint`), and `red_upperC` identifies its reduction
  with the lower corner unipotent `lowerUnip (resCorner Z)` of the module `FiniteMackey`, the
  late indices being those outside the first `j` blocks. For an integral corner `Z`,
  `resCorner Z = 0` exactly when every entry of `Z` lies in the maximal ideal
  (`resCorner_eq_zero_iff`). Integrality is needed here: `resCorner` applies `resF`, the residue map
  extended by zero to non-integral elements.
- `stdType_test`: suppose no block among the first `j` of `E` carries the label of a later block.
  Then every nonzero intertwiner `g` from `stdType E` into a representation `π` of `GL_n(F)`
  admits a linear retraction `ψ` satisfying the hypotheses of `eq_zero_of_compression_eq_zero`.
  The values of `g` are fixed by the principal congruence subgroup, and `g` is equivariant for the
  parabolic over `k_F` acting through `descended π`. It is injective because the inflated Levi
  tensor is irreducible. A `P(k_F)`-equivariant left inverse (`exists_equivariant_leftInverse`)
  extended linearly to the whole space is `ψ`. Invariance under `J1` holds because `J1` reduces
  into the unipotent radical, where the type is trivial. The translates by corners not congruent
  to zero are killed by `retraction_lowerUnip_eq_zero`.
