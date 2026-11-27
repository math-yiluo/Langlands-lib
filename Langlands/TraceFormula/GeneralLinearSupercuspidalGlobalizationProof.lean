import Langlands.Automorphic.GeneralLinearFullAEL2CuspidalCompactnessProof
import Langlands.Automorphic.GroupSchemeFullAEL2CuspidalDecompositionProof
import Langlands.TraceFormula.GeneralLinearSupercuspidalCommonVector
import Langlands.TraceFormula.GeneralLinearSupercuspidalGlobalizationReduction
import Langlands.TraceFormula.GeneralLinearSupercuspidalSummandExtraction
import Langlands.TraceFormula.UnitarySchurHilbertSumProof

/-! # Globalization of supercuspidal representations of `GL_n` -/

noncomputable section

universe u w

open CategoryTheory AlgebraicGeometry MeasureTheory
open scoped CategoryTheory.MonObj
open Langlands.Global Langlands.GroupScheme
open Langlands.Automorphic.GroupSchemeFunctions

namespace Langlands.TraceFormula

set_option backward.isDefEq.respectTransparency false in
set_option maxHeartbeats 3500000 in
/-- Finitely many prescribed supercuspidals occur up to unramified twists in one
actual cuspidal summand with the required common level and compressed traces. -/
theorem generalLinearSupercuspidalGlobalization :
    GeneralLinearSupercuspidalGlobalizationStatement.{u, w} := by
  apply generalLinearSupercuspidalGlobalization_of_positiveRankOccurrence
  intro K _ _ n hn hPD hG T i hi _ I _ e hc _ _ _ _ _ Sc hSc vaux hvaux V _ _ ρ hρ
  let G := GroupScheme.GeneralLinear.groupScheme (Fin n) (CommRingCat.of K)
  let : IsAffine G.X.left := GroupScheme.GeneralLinear.isAffine_groupScheme _ _
  let : Smooth G.X.hom := GroupScheme.GeneralLinear.smoothStatement _ _
  let S := fullAEL2CuspidalSubmodule K G hPD hG T i hi I e hc
  obtain ⟨A, hA, hsum, _⟩ := groupSchemeFullAEL2CuspidalDecomposition K G hPD hG T i hi I e hc
    (generalLinearFullAEL2CuspidalCompactness K n hPD hG T i hi I e hc)
  let : ∀ P : A, CompleteSpace P.val := fun P => (hA P.val P.property).2.1.completeSpace_coe
  have htotal : (⨆ P : A, (P.val : Submodule ℂ S)).topologicalClosure = ⊤ := by
    have htop : LinearMap.range hsum.OrthogonalFamily.linearIsometry.toLinearMap = ⊤ :=
      LinearMap.range_eq_top.mpr hsum.surjective_isometry
    rw [hsum.OrthogonalFamily.range_linearIsometry] at htop
    simpa only [Submodule.subtypeₗᵢ_toLinearMap, Submodule.range_subtype] using htop
  obtain ⟨x, hx, hfix, hj⟩ := exists_supercuspidalCommonVector K n hPD hG T i hi I e hc
    hn Sc hSc vaux hvaux V ρ hρ
  exact extract_supercuspidalSummand_of_determinantUnitOccurrence K n hPD hG T i hi I e hc
    hn unitarySchurHilbertSum A hA htotal Sc vaux V ρ (fun v hv => ⟨(hρ v hv).1, (hρ v hv).2.1⟩)
    x hx hfix hj

end Langlands.TraceFormula
