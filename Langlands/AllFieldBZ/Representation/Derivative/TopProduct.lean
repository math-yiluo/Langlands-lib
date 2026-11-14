import Langlands.AllFieldBZ.Representation.Derivative.GeneralLinearDerivativeLeibnizFiltrationProof
import Langlands.Representation.Derivative.TopProduct

/-!
# All-field port of `Langlands.Representation.Derivative.TopProduct`

Mechanical port of the field-dependent declarations of the p-adic module
`Langlands.Representation.Derivative.TopProduct` to an arbitrary nonarchimedean local field
(`Langlands.AllFieldBZ.LocalFieldPackage`). See the paired Markdown.
-/
noncomputable section
open CategoryTheory
open scoped TensorProduct
namespace Langlands.AllFieldBZ.Derivative
open Langlands.Derivative hiding GeneralLinearDerivativeExactnessStatement GeneralLinearDerivativeLeibnizFiltrationStatement HasNonzeroDerivative IsHomogeneous LeftMixedProductDerivative LeftMixedProductDerivativeIso LeftMixedProductDerivativeVanishing MirabolicDerivativeDetection MirabolicProductMinusCompatibilityStatement MirabolicProductRestrictionStatement RightMixedProductDerivativeFiltrationStatement RightMixedProductPhiMinusDetection binaryNormalizedProductLeftZeroSwapIso binaryNormalizedProductSwapZeroIso binaryRightZeroDerivativeIso generalLinearDerivative generalLinearDerivativeExactness generalLinearDerivativeLeibnizFiltration generalLinearDerivativeLeibnizFiltration_left_zero generalLinearDerivativeLeibnizFiltration_pos generalLinearDerivativeLeibnizFiltration_right_zero generalLinearDerivativeLeibnizFiltration_zero generalLinearDerivativePositive generalLinearDerivativePositive_eq generalLinearDerivativePositive_mapsShortExact generalLinearDerivativePositive_obj generalLinearDerivative_of_pos generalLinearDerivative_succ generalLinearDerivative_succ_obj generalLinearDerivative_top_succ generalLinearDerivative_zero generalLinearRankCast generalLinearRankCastDerivativeIso generalLinearRankCastRestrictionIso generalLinearRankCast_mapsShortExact generalLinearRankCast_refl generalLinearRankCast_symm_comp generalLinearRankCast_toRep generalLinearRankCast_trans generalLinearRepRankCast generalLinearRestriction generalLinearRestrictionDerivativeIso generalLinearRestriction_map_apply generalLinearRestriction_map_toLinearMap generalLinearRestriction_mapsShortExact hasNonzeroDerivative_iff isGluedFromFamily_repRankCast isHomogeneous_of_subsingleton isoRankCastOfEquiv le_level_of_hasNonzeroDerivative leftMixedProductDerivative leftMixedProductDerivativeIso leftMixedProductDerivativeVanishing leftMixedProduct_rankCast leibnizPiece leibnizPiece_obj leibnizPiece_zero leibnizPositivePieceIso leibnizPositiveSmoothPieceIso leibnizRestrictedProductSourceIso leibnizRestrictionDerivativeExact leibnizRestrictionDerivativeQuotient leibnizRestrictionDerivativeSubobject leibnizRestrictionQuotientPiece leibnizRestrictionQuotientPieceIso leibnizRestrictionQuotient_glued leibnizRestrictionQuotient_subsingleton leibnizRestrictionSubobjectPiece leibnizRestrictionSubobjectSourceIso leibnizRestrictionSubobject_glued leibnizSource leibnizSourceLeftZeroIso leibnizSourceLeftZeroPieceIso leibnizSourceRightZeroIso leibnizSourceRightZeroPieceIso leibnizSource_glued_pos leibnizSource_zero leibnizZeroFirstSmoothPieceIso level level_eq_iff level_eq_zero_iff level_eq_zero_of_subsingleton level_le mirabolicDerivative mirabolicDerivativeDetection mirabolicDerivativeOfOrder mirabolicDerivativeOfOrder_eq mirabolicDerivativeOfOrder_obj mirabolicDerivativeOfOrder_obj_subsingleton mirabolicDerivativeOfOrder_one mirabolicDerivativeOfOrder_top mirabolicDerivative_eq mirabolicDerivative_mapsShortExact mirabolicDerivative_obj_subsingleton mirabolicDerivative_succ mirabolicDerivative_zero mirabolicProductRestriction mirabolicRankCast mirabolicRankCastDerivativeIso mirabolicRankCast_obj_subsingleton mirabolicRankCast_refl mirabolicRankCast_symm_comp mirabolicRankCast_trans phiMinusIterate phiMinusIterate_mapsShortExact phiMinusIterate_obj_subsingleton phiMinusIterate_succ phiMinusIterate_zero phiMinus_rankCast rightMixedDerivativePiece rightMixedDerivativeSource rightMixedProductDerivativeFiltration rightMixedProductDerivativeFiltration_zero topProductIso topProductTensorEquiv
universe uF uV uW

variable {F : LocalFieldPackage.{uF}}
  (T : F.TopologicalData)
  (ψ : @HarmonicAnalysis.UnitaryAdditiveCharacter F.Carrier _ T.topology)

/-- The top-order Leibniz filtration gives an actual natural isomorphism with
the product of the two top derivatives, in every rank. -/
def topProductIso (a b : ℕ) :
    letI := T.topology
    leibnizSource.{uF, uV} T ψ a b (a + b) le_rfl ≅
      leibnizPiece T ψ a b (a + b) (topLeibnizIndex a b) := by
  letI := T.topology
  exact Classical.choice (by
    obtain ⟨e, h⟩ :=
      generalLinearDerivativeLeibnizFiltration.{uF, uV} F T ψ a b (a + b) le_rfl
    exact ⟨h.isoOfLengthOne (by simp) (e (topLeibnizIndex a b)) ≪≫
      eqToIso (congrArg (leibnizPiece T ψ a b (a + b))
        (e.symm_apply_apply (topLeibnizIndex a b)))⟩)

private def _root_.Langlands.Derivative.rankCastCarrierEquiv {a b : ℕ} (h : a = b)
    (A : letI := T.topology;
      SmoothRep.{0, uF, uW} ℂ (GeneralLinear a F.Carrier)) :
    letI := T.topology
    (generalLinearRankCast T h).obj A ≃ₗ[ℂ] A := by
  subst b
  exact LinearEquiv.refl ℂ A

/-- The entire carrier of the top derivative of a binary product is linearly
equivalent to the entire tensor product of the factor top-derivative carriers.
No finite-dimensionality, irreducibility or positive-rank hypothesis is used. -/
def topProductTensorEquiv {a b : ℕ}
    (A : letI := T.topology;
      SmoothRep.{0, uF, uV} ℂ (GeneralLinear a F.Carrier))
    (B : letI := T.topology;
      SmoothRep.{0, uF, uV} ℂ (GeneralLinear b F.Carrier)) :
    letI := T.topology
    ((generalLinearDerivative T ψ (a + b) (a + b) le_rfl).obj
        ((T.binaryNormalizedProductFunctor a b).obj (A, B))) ≃ₗ[ℂ]
      ((generalLinearDerivative T ψ a a le_rfl).obj A) ⊗[ℂ]
        ((generalLinearDerivative T ψ b b le_rfl).obj B) := by
  letI := T.topology
  exact (Representation.equivOfIso ((topProductIso T ψ a b).app (A, B))).toLinearEquiv
    |>.trans (rankCastCarrierEquiv T
      (leibnizIndices_rank (topLeibnizIndex a b).property) _)
    |>.trans (T.binaryZeroZeroTensorEquiv (Nat.sub_self a) (Nat.sub_self b)
      (((generalLinearDerivative T ψ a a le_rfl).obj A),
        ((generalLinearDerivative T ψ b b le_rfl).obj B))).toLinearEquiv

end Langlands.AllFieldBZ.Derivative
