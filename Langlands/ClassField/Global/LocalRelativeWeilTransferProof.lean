import Langlands.ClassField.Global.LocalRelativeWeilTransferReduction
import Langlands.ClassFieldTheory.Local.WeilTransferReciprocityProof

/-! # Local transfer reciprocity for local relative Weil maps

For every class family, every Galois extension `E / F` of number fields and every local
map `ι : W_{F_z} → W_{E/F}` at a place `w | z`, the transfer of `ι` to `C_F` is inverse
geometric local reciprocity at `z`. The proof combines the reduction
`localTransferReciprocity_of_square` with the published local transfer/inclusion square
`LocalClassField.extensionWeilTransferReciprocity`. -/

namespace Langlands.ClassField.Global.RelativeWeilGroup

universe u

/-- Tate (1979), (1.6.1) with `E = F`, for relative Weil groups: the transfer to `C_F` of a
local map `ι : W_{F_z} → W_{E/F}` is inverse geometric local reciprocity at `z`. -/
theorem localTransferReciprocity : LocalTransferReciprocityStatement.{u} :=
  localTransferReciprocity_of_square LocalClassField.extensionWeilTransferReciprocity.{u, u}

end Langlands.ClassField.Global.RelativeWeilGroup
