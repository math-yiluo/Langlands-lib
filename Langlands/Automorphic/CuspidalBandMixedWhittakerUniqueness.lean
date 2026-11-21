import Langlands.Automorphic.CuspidalBandMixedMultiplicityOneStatement
import Langlands.Automorphic.CuspidalCompletionMixedWhittakerUniqueness
import Langlands.Automorphic.CuspidalArchimedeanWhittakerSliceBridge
import Langlands.Global.RankinSelberg.CuspidalBandMixedSourceDensity

/-! # Mixed Whittaker uniqueness on the actual cuspidal band completion -/

noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 25000
set_option Elab.async false

namespace Langlands.Automorphic

open Langlands.Archimedean OperatorDeterminantSlice
open Langlands.Global.RankinSelbergGlobal.ArchimedeanWhittakerRegularity
universe u

/-- Local continuous unitary Whittaker uniqueness implies uniqueness of the
mixed functionals on the actual cuspidal determinant-band completion. -/
def CuspidalBandMixedWhittakerUniquenessFromLocalStatement : Prop :=
  UnitaryWhittakerMultiplicityOneStatement.{u} → CuspidalBandMixedWhittakerUniquenessStatement.{u}

theorem cuspidalBandMixedWhittakerUniquenessFromLocal :
    CuspidalBandMixedWhittakerUniquenessFromLocalStatement.{u} := by
  intro hUnique F _ _ _ r T χ hχ hTχ b hb
  let B := adelicCompletion T χ hχ hTχ b hb
  let j := toHilbertMixed T χ hχ hTχ b hb
  have harch : CompletionArchimedeanWhittakerSlices T B :=
    cuspidalBandArchimedeanWhittakerSliceBridge hUnique F r T χ hχ hTχ b hb
  exact completionMixedWhittakerUniqueness T B j (toBandHilbertSmooth T χ hχ hTχ b hb)
    (fun _ => rfl) (bandDenseFixedImages T χ hχ hTχ b hb)
    (fun η hη => harch η hη j (fun _ => rfl))

end Langlands.Automorphic
