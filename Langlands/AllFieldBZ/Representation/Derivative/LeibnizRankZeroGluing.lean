import Langlands.AllFieldBZ.Representation.Derivative.LeibnizRankZeroBoundary
import Langlands.Representation.Derivative.LeibnizRankZeroGluing

/-!
# All-field port of `Langlands.Representation.Derivative.LeibnizRankZeroGluing`

Mechanical port of the field-dependent declarations of the p-adic module
`Langlands.Representation.Derivative.LeibnizRankZeroGluing` to an arbitrary nonarchimedean local field
(`Langlands.AllFieldBZ.LocalFieldPackage`). See the paired Markdown.
-/
noncomputable section
open CategoryTheory
namespace Langlands.AllFieldBZ.Derivative
open Langlands.Derivative hiding GeneralLinearDerivativeLeibnizFiltrationStatement HasNonzeroDerivative IsHomogeneous binaryNormalizedProductLeftZeroSwapIso binaryNormalizedProductSwapZeroIso binaryRightZeroDerivativeIso generalLinearDerivative generalLinearDerivativeLeibnizFiltration_left_zero generalLinearDerivativeLeibnizFiltration_right_zero generalLinearDerivativePositive generalLinearDerivativePositive_eq generalLinearDerivativePositive_obj generalLinearDerivative_of_pos generalLinearDerivative_succ generalLinearDerivative_succ_obj generalLinearDerivative_top_succ generalLinearDerivative_zero generalLinearRankCast generalLinearRankCastDerivativeIso generalLinearRankCastRestrictionIso generalLinearRankCast_refl generalLinearRankCast_symm_comp generalLinearRankCast_trans generalLinearRestriction generalLinearRestrictionDerivativeIso generalLinearRestriction_map_apply generalLinearRestriction_map_toLinearMap hasNonzeroDerivative_iff isHomogeneous_of_subsingleton isoRankCastOfEquiv le_level_of_hasNonzeroDerivative leibnizPiece leibnizPiece_obj leibnizSource leibnizSourceLeftZeroIso leibnizSourceLeftZeroPieceIso leibnizSourceRightZeroIso leibnizSourceRightZeroPieceIso level level_eq_iff level_eq_zero_iff level_eq_zero_of_subsingleton level_le mirabolicDerivative mirabolicDerivativeOfOrder mirabolicDerivativeOfOrder_eq mirabolicDerivativeOfOrder_obj mirabolicDerivativeOfOrder_obj_subsingleton mirabolicDerivativeOfOrder_one mirabolicDerivativeOfOrder_top mirabolicDerivative_eq mirabolicDerivative_obj_subsingleton mirabolicDerivative_succ mirabolicDerivative_zero mirabolicRankCast mirabolicRankCastDerivativeIso mirabolicRankCast_obj_subsingleton mirabolicRankCast_refl phiMinusIterate phiMinusIterate_obj_subsingleton phiMinusIterate_succ phiMinusIterate_zero
universe uF uV

variable {F : LocalFieldPackage.{uF}}

/-- Complete feasible-index gluing when the first input has rank zero. -/
theorem generalLinearDerivativeLeibnizFiltration_left_zero (T : F.TopologicalData)
    (ψ : @HarmonicAnalysis.UnitaryAdditiveCharacter F.Carrier _ T.topology)
    (b d : ℕ) (hd : d ≤ 0 + b) :
    letI := T.topology
    ∃ e : LeibnizIndex 0 b d ≃ Fin (leibnizIndices 0 b d).card,
      IsGluedFrom (leibnizSource.{uF, uV} T ψ 0 b d hd)
        (fun i => leibnizPiece T ψ 0 b d (e.symm i)) := by
  let _ := T.topology
  let e := (leibnizIndices 0 b d).equivFin
  refine ⟨e, ?_⟩
  apply isGluedFrom_of_length_eq_one (by rw [leibnizIndices_left_zero hd]; simp)
  intro i
  exact leibnizSourceLeftZeroPieceIso T ψ hd (e.symm i)

/-- Complete feasible-index gluing when the second input has rank zero. -/
theorem generalLinearDerivativeLeibnizFiltration_right_zero (T : F.TopologicalData)
    (ψ : @HarmonicAnalysis.UnitaryAdditiveCharacter F.Carrier _ T.topology)
    (a d : ℕ) (hd : d ≤ a + 0) :
    letI := T.topology
    ∃ e : LeibnizIndex a 0 d ≃ Fin (leibnizIndices a 0 d).card,
      IsGluedFrom (leibnizSource.{uF, uV} T ψ a 0 d hd)
        (fun i => leibnizPiece T ψ a 0 d (e.symm i)) := by
  let _ := T.topology
  let e := (leibnizIndices a 0 d).equivFin
  refine ⟨e, ?_⟩
  apply isGluedFrom_of_length_eq_one (by rw [leibnizIndices_right_zero hd]; simp)
  intro i
  exact leibnizSourceRightZeroPieceIso T ψ hd (e.symm i)

end Langlands.AllFieldBZ.Derivative
