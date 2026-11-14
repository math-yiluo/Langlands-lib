import Langlands.AllFieldBZ.Representation.Derivative.GeneralLinearDerivativeLeibnizBoundary
import Langlands.AllFieldBZ.Representation.Derivative.LeibnizPositiveGluing
import Langlands.AllFieldBZ.Representation.Derivative.LeibnizRankZeroGluing
import Langlands.AllFieldBZ.Representation.Derivative.RightMixedProductDerivativeFiltrationProof
import Langlands.Representation.Derivative.GeneralLinearDerivativeLeibnizFiltrationProof

/-!
# All-field port of `Langlands.Representation.Derivative.GeneralLinearDerivativeLeibnizFiltrationProof`

Mechanical port of the field-dependent declarations of the p-adic module
`Langlands.Representation.Derivative.GeneralLinearDerivativeLeibnizFiltrationProof` to an arbitrary nonarchimedean local field
(`Langlands.AllFieldBZ.LocalFieldPackage`). See the paired Markdown.
-/
namespace Langlands.AllFieldBZ.Derivative
open Langlands.Derivative hiding GeneralLinearDerivativeExactnessStatement GeneralLinearDerivativeLeibnizFiltrationStatement HasNonzeroDerivative IsHomogeneous LeftMixedProductDerivative LeftMixedProductDerivativeIso LeftMixedProductDerivativeVanishing MirabolicDerivativeDetection MirabolicProductMinusCompatibilityStatement MirabolicProductRestrictionStatement RightMixedProductDerivativeFiltrationStatement RightMixedProductPhiMinusDetection binaryNormalizedProductLeftZeroSwapIso binaryNormalizedProductSwapZeroIso binaryRightZeroDerivativeIso generalLinearDerivative generalLinearDerivativeExactness generalLinearDerivativeLeibnizFiltration generalLinearDerivativeLeibnizFiltration_left_zero generalLinearDerivativeLeibnizFiltration_pos generalLinearDerivativeLeibnizFiltration_right_zero generalLinearDerivativeLeibnizFiltration_zero generalLinearDerivativePositive generalLinearDerivativePositive_eq generalLinearDerivativePositive_mapsShortExact generalLinearDerivativePositive_obj generalLinearDerivative_of_pos generalLinearDerivative_succ generalLinearDerivative_succ_obj generalLinearDerivative_top_succ generalLinearDerivative_zero generalLinearRankCast generalLinearRankCastDerivativeIso generalLinearRankCastRestrictionIso generalLinearRankCast_mapsShortExact generalLinearRankCast_refl generalLinearRankCast_symm_comp generalLinearRankCast_toRep generalLinearRankCast_trans generalLinearRepRankCast generalLinearRestriction generalLinearRestrictionDerivativeIso generalLinearRestriction_map_apply generalLinearRestriction_map_toLinearMap generalLinearRestriction_mapsShortExact hasNonzeroDerivative_iff isGluedFromFamily_repRankCast isHomogeneous_of_subsingleton isoRankCastOfEquiv le_level_of_hasNonzeroDerivative leftMixedProductDerivative leftMixedProductDerivativeIso leftMixedProductDerivativeVanishing leftMixedProduct_rankCast leibnizPiece leibnizPiece_obj leibnizPiece_zero leibnizPositivePieceIso leibnizPositiveSmoothPieceIso leibnizRestrictedProductSourceIso leibnizRestrictionDerivativeExact leibnizRestrictionDerivativeQuotient leibnizRestrictionDerivativeSubobject leibnizRestrictionQuotientPiece leibnizRestrictionQuotientPieceIso leibnizRestrictionQuotient_glued leibnizRestrictionQuotient_subsingleton leibnizRestrictionSubobjectPiece leibnizRestrictionSubobjectSourceIso leibnizRestrictionSubobject_glued leibnizSource leibnizSourceLeftZeroIso leibnizSourceLeftZeroPieceIso leibnizSourceRightZeroIso leibnizSourceRightZeroPieceIso leibnizSource_glued_pos leibnizSource_zero leibnizZeroFirstSmoothPieceIso level level_eq_iff level_eq_zero_iff level_eq_zero_of_subsingleton level_le mirabolicDerivative mirabolicDerivativeDetection mirabolicDerivativeOfOrder mirabolicDerivativeOfOrder_eq mirabolicDerivativeOfOrder_obj mirabolicDerivativeOfOrder_obj_subsingleton mirabolicDerivativeOfOrder_one mirabolicDerivativeOfOrder_top mirabolicDerivative_eq mirabolicDerivative_mapsShortExact mirabolicDerivative_obj_subsingleton mirabolicDerivative_succ mirabolicDerivative_zero mirabolicProductRestriction mirabolicRankCast mirabolicRankCastDerivativeIso mirabolicRankCast_obj_subsingleton mirabolicRankCast_refl mirabolicRankCast_symm_comp mirabolicRankCast_trans phiMinusIterate phiMinusIterate_mapsShortExact phiMinusIterate_obj_subsingleton phiMinusIterate_succ phiMinusIterate_zero phiMinus_rankCast rightMixedDerivativePiece rightMixedDerivativeSource rightMixedProductDerivativeFiltration rightMixedProductDerivativeFiltration_zero
universe uF uV

/-- The actual natural Leibniz filtration in every rank and every valid order. -/
theorem generalLinearDerivativeLeibnizFiltration
    (F : LocalFieldPackage.{uF}) (T : F.TopologicalData) :
    GeneralLinearDerivativeLeibnizFiltrationStatement.{uF, uV} F T := by
  intro ψ a b d hd
  cases d with
  | zero =>
      exact generalLinearDerivativeLeibnizFiltration_zero T ψ a b hd
  | succ d =>
      cases a with
      | zero =>
          exact generalLinearDerivativeLeibnizFiltration_left_zero T ψ b (d + 1) hd
      | succ m =>
          cases b with
          | zero =>
              exact generalLinearDerivativeLeibnizFiltration_right_zero T ψ (m + 1) (d + 1) hd
          | succ n =>
              exact generalLinearDerivativeLeibnizFiltration_pos T
                (leftMixedProductDerivativeIso.{uF, uV} F T)
                (leftMixedProductDerivativeVanishing.{uF, uV} F T)
                (rightMixedProductDerivativeFiltration.{uF, uV} F T)
                ψ m n (d + 1) ⟨Nat.succ_pos d, hd⟩

end Langlands.AllFieldBZ.Derivative
