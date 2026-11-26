import Langlands.Global.RankinSelberg.RealWhittakerUniformFiniteGeneration
import Langlands.Representation.Archimedean.RealStandardFiniteGeneration

/-! # Uniform growth in the exact real Whittaker model -/

noncomputable section

open Langlands.LocalFactor.Archimedean

set_option autoImplicit false

namespace Langlands.Global.RankinSelbergGlobal

/-- Every coefficient map for a rank-correct real block list has one height exponent
for all its source vectors. -/
def RealWhittakerIntertwinerUniformGrowthStatement : Prop :=
  ∀ (r : ℕ) (ds : List RealBlock), realRank ds = r + 1 →
    ∀ (a : ℝˣ) (B : Automorphic.realStandardKFinite (r + 1) ds →ₗ[ℂ]
      (Langlands.GeneralLinear (r + 1) ℝ → ℂ)),
      IsRealWhittakerIntertwiner r ds a B → IsRealUniformWhittakerIntertwiner r ds a B

theorem realWhittakerIntertwinerUniformGrowth : RealWhittakerIntertwinerUniformGrowthStatement := by
  intro r ds hRank a B hB
  obtain ⟨F, hdim, hF⟩ := Archimedean.realStandardFiniteGeneration (r + 1) ds hRank
  let _ : FiniteDimensional ℂ F := hdim
  exact RealUniformWhittaker.intertwiner_of_wordSpan_eq_top hB F hF

theorem realWhittakerModels_eq (r : ℕ) (ds : List RealBlock) (hRank : realRank ds = r + 1)
    (a : ℝˣ) : realWhittakerModel r ds a = realUniformWhittakerModel r ds a := by
  refine le_antisymm ?_ (RealUniformWhittaker.model_le_model ds a)
  refine iSup_le fun B => iSup_le fun hB => ?_
  exact le_iSup_of_le B (le_iSup_of_le (realWhittakerIntertwinerUniformGrowth r ds hRank a B hB) le_rfl)

end Langlands.Global.RankinSelbergGlobal
