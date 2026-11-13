import Langlands.VirtualRepresentation.Global.RelativeWeilLocalRestrictionReduction
import Langlands.ClassFieldTheory.Local.WeilTransferReciprocityProof

/-!
# The local restriction formula for induced relative Weil representations

The published reduction `localInducedRestriction_of_extensionSquare`, applied to the
proved local transfer/inclusion square at equal universes.
-/

noncomputable section

set_option autoImplicit false

universe uV u

namespace Langlands.ClassField.Global.RelativeWeilGroup

/-- **Local restriction formula** (Tate (1979), (2.3.5) with (1.6.1), for relative Weil
groups). For every class family with the restriction compatibility, every tower
`F ⊆ K ⊆ E` with `E / F` Galois and every local map `ι : W_{F_z} → W_{E/F}` at a place
above a finite place `z`, the local restriction formula holds for `ι`. -/
theorem localInducedRestriction : LocalInducedRestrictionStatement.{uV, u} :=
  localInducedRestriction_of_extensionSquare
    LocalClassField.extensionWeilTransferReciprocity.{u, u}

end Langlands.ClassField.Global.RelativeWeilGroup
