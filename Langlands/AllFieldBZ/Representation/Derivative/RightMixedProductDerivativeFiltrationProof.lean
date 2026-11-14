import Langlands.AllFieldBZ.Representation.Derivative.LeftMixedProductDerivativeProof
import Langlands.AllFieldBZ.Representation.Derivative.MirabolicProductMinusRightPhi
import Langlands.AllFieldBZ.Representation.Derivative.RightMixedProductDerivativePositive
import Langlands.AllFieldBZ.Representation.Derivative.RightMixedProductZeroRank
import Langlands.Representation.Derivative.RightMixedProductDerivativeFiltrationProof

/-!
# All-field port of `Langlands.Representation.Derivative.RightMixedProductDerivativeFiltrationProof`

Mechanical port of the field-dependent declarations of the p-adic module
`Langlands.Representation.Derivative.RightMixedProductDerivativeFiltrationProof` to an arbitrary nonarchimedean local field
(`Langlands.AllFieldBZ.LocalFieldPackage`). See the paired Markdown.
-/
namespace Langlands.AllFieldBZ.Derivative
open Langlands.Derivative hiding HasNonzeroDerivative IsHomogeneous LeftMixedProductDerivative LeftMixedProductDerivativeIso LeftMixedProductDerivativeVanishing MirabolicDerivativeDetection MirabolicProductMinusCompatibilityStatement RightMixedProductDerivativeFiltrationStatement RightMixedProductPhiMinusDetection generalLinearDerivative generalLinearDerivativePositive generalLinearDerivativePositive_eq generalLinearDerivativePositive_obj generalLinearDerivative_of_pos generalLinearDerivative_succ generalLinearDerivative_succ_obj generalLinearDerivative_top_succ generalLinearDerivative_zero generalLinearRankCast generalLinearRankCast_refl generalLinearRankCast_symm_comp generalLinearRankCast_trans generalLinearRestriction generalLinearRestriction_map_apply generalLinearRestriction_map_toLinearMap hasNonzeroDerivative_iff isHomogeneous_of_subsingleton le_level_of_hasNonzeroDerivative leftMixedProductDerivative leftMixedProductDerivativeIso leftMixedProductDerivativeVanishing leftMixedProduct_rankCast level level_eq_iff level_eq_zero_iff level_eq_zero_of_subsingleton level_le mirabolicDerivative mirabolicDerivativeDetection mirabolicDerivativeOfOrder mirabolicDerivativeOfOrder_eq mirabolicDerivativeOfOrder_obj mirabolicDerivativeOfOrder_obj_subsingleton mirabolicDerivativeOfOrder_one mirabolicDerivativeOfOrder_top mirabolicDerivative_eq mirabolicDerivative_obj_subsingleton mirabolicDerivative_succ mirabolicDerivative_zero mirabolicRankCast mirabolicRankCast_obj_subsingleton mirabolicRankCast_refl mirabolicRankCast_symm_comp mirabolicRankCast_trans phiMinusIterate phiMinusIterate_obj_subsingleton phiMinusIterate_succ phiMinusIterate_zero phiMinus_rankCast rightMixedDerivativePiece rightMixedDerivativeSource rightMixedProductDerivativeFiltration rightMixedProductDerivativeFiltration_zero
universe uF uV

/-- BZ77 4.14(b), with the internal `k = 0` extension: the actual finite natural
filtration of every derivative of every right mixed product. -/
theorem rightMixedProductDerivativeFiltration
    (F : LocalFieldPackage.{uF}) (T : F.TopologicalData) :
    RightMixedProductDerivativeFiltrationStatement.{uF, uV} F T := by
  intro ψ k
  cases k with
  | zero => exact rightMixedProductDerivativeFiltration_zero T ψ
  | succ k =>
    exact RightMixedDerivative.filtration_pos T ψ
      (MirabolicProductMinus.rightPsiCompatibility.{uF, uV} T)
      (MirabolicProductMinus.rightPhiShortExact.{uF, uV} T)
      (leftMixedProductDerivativeIso.{uF, uV} F T)
      (leftMixedProductDerivativeVanishing.{uF, uV} F T)
      (Mirabolic.minusExactness.{uF, max uF uV} F T) k

end Langlands.AllFieldBZ.Derivative
