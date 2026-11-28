# Unit groups of standard orders and reduction modulo the maximal ideal

Module `Langlands.BushnellKutzko.SplitTypeJacquet.StandardReduction`. Here `F` is a field with a
valuative relation, `n = m + 1`, `Kint F m` is `GL_n(𝔬_F)` (the Library's
`Conductor.integralSubgroup`) and `red F m : Kint F m →* GL_n(k_F)` is entrywise reduction
(`IntegralReduction.reduction`). For a block shape `B`, `blkOf B` is its block function.

- `red_mem_parabolic_iff`: an element of `GL_n(𝔬_F)` reduces into the standard parabolic
  `B.parabolic k_F` exactly when it lies in `J0 F (blkOf B)`;
  `red_mem_unipotentSubgroup_of_mem_J1`: elements of `J1 F (blkOf B)` reduce into its unipotent
  radical. `resF` is the residue map extended by zero, with `red_apply_resF`.
- `mem_principalLevel_one_iff`: the principal congruence subgroup of level one
  (`Conductor.principalLevelSubgroup F m 1`) is the kernel of reduction; it lies in every `J1`
  (`principalLevel_one_le_J1`) and is normalized by `GL_n(𝔬_F)`.
- For a representation `π` of `GL_n(F)`, `fixK1 π` are the vectors fixed by the principal
  congruence subgroup of level one. `GL_n(𝔬_F)` acts on them (`kintAction`), and the action
  descends along reduction to `descended π : Representation ℂ (GL_n(k_F)) (fixK1 π)` with
  `descended_red`: `descended π (red g) x = π g x`. The descent uses
  `MonoidHom.liftOfRightInverse` with the integral lift of residue matrices.
