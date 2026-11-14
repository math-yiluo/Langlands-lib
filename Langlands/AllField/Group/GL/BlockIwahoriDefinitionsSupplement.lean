import Langlands.Group.GL.BlockIwahoriDefinitions
import Langlands.AllField.Group.GL.BlockIwahoriDefinitions
import Langlands.AllField.Group.GL.NormalizedCharacterSupplement
noncomputable section

open scoped NNReal

namespace Langlands.AllField.GeneralLinear.BlockShape
open Langlands.GeneralLinear.BlockShape hiding HasBlockIwahoriFactorization IsWeaklyContracting
open Langlands.AllField.GeneralLinear.BlockShape
open Langlands.GeneralLinear
open Langlands.AllField.GeneralLinear

universe u

variable {n : ℕ} (B : GeneralLinear.BlockShape n) (R : Type u) [CommRing R]

variable (K : Subgroup (GeneralLinear n R))

section Padic

variable {F : Type u} [Field F] (T : LocalFieldData F)

theorem HasBlockIwahoriFactorization.bijective :
    letI := T.topology
    ∀ {K : OpenSubgroup (GeneralLinear n F)},
      (Langlands.AllField.GeneralLinear.BlockShape.HasBlockIwahoriFactorization B) T K →
        Function.Bijective (B.iwahoriProduct F K.toSubgroup) := by
  let := T.topology
  intro K hK
  exact hK.1

end Padic
end Langlands.AllField.GeneralLinear.BlockShape
