import Langlands.AllFieldBZ.Representation.Derivative.LeftMixedProductHigher
import Langlands.AllFieldBZ.Representation.Derivative.LeftMixedProductVanishing
import Langlands.AllFieldBZ.Representation.Derivative.MirabolicProductMinusLeftPhi
import Langlands.Representation.Derivative.LeftMixedProductDerivativeProof

/-!
# All-field port of `Langlands.Representation.Derivative.LeftMixedProductDerivativeProof`

Mechanical port of the field-dependent declarations of the p-adic module
`Langlands.Representation.Derivative.LeftMixedProductDerivativeProof` to an arbitrary nonarchimedean local field
(`Langlands.AllFieldBZ.LocalFieldPackage`). See the paired Markdown.
-/
namespace Langlands.AllFieldBZ.Derivative
open Langlands.Derivative hiding HasNonzeroDerivative IsHomogeneous LeftMixedProductDerivative LeftMixedProductDerivativeIso LeftMixedProductDerivativeVanishing MirabolicProductMinusCompatibilityStatement RightMixedProductPhiMinusDetection generalLinearDerivative generalLinearDerivativePositive generalLinearDerivativePositive_eq generalLinearDerivativePositive_obj generalLinearDerivative_of_pos generalLinearDerivative_succ generalLinearDerivative_succ_obj generalLinearDerivative_top_succ generalLinearDerivative_zero generalLinearRankCast generalLinearRankCast_refl generalLinearRankCast_symm_comp generalLinearRankCast_trans generalLinearRestriction generalLinearRestriction_map_apply generalLinearRestriction_map_toLinearMap hasNonzeroDerivative_iff isHomogeneous_of_subsingleton le_level_of_hasNonzeroDerivative leftMixedProductDerivative leftMixedProductDerivativeIso leftMixedProductDerivativeVanishing leftMixedProduct_rankCast level level_eq_iff level_eq_zero_iff level_eq_zero_of_subsingleton level_le mirabolicDerivative mirabolicDerivativeOfOrder mirabolicDerivativeOfOrder_eq mirabolicDerivativeOfOrder_obj mirabolicDerivativeOfOrder_obj_subsingleton mirabolicDerivativeOfOrder_one mirabolicDerivativeOfOrder_top mirabolicDerivative_eq mirabolicDerivative_obj_subsingleton mirabolicDerivative_succ mirabolicDerivative_zero mirabolicRankCast mirabolicRankCast_obj_subsingleton mirabolicRankCast_refl mirabolicRankCast_symm_comp mirabolicRankCast_trans phiMinusIterate phiMinusIterate_obj_subsingleton phiMinusIterate_succ phiMinusIterate_zero phiMinus_rankCast
universe uF uV

/-- BZ77 4.14(a): the exact all-rank natural comparison and vanishing statement. -/
theorem leftMixedProductDerivative
    (F : LocalFieldPackage.{uF}) (T : F.TopologicalData) :
    LeftMixedProductDerivative.{uF, uV} F T :=
  ⟨LeftMixedProductHigher.leftMixedProductDerivativeIso T
      (MirabolicProductMinus.leftPhiCompatibility T),
    LeftMixedProductVanishing.leftMixedProductDerivativeVanishing_of_leftPhiCompatibility T
      (MirabolicProductMinus.leftPhiCompatibility T)⟩

/-- The natural comparison in every GL rank and every order `1 ≤ i ≤ r + 1`. -/
theorem leftMixedProductDerivativeIso
    (F : LocalFieldPackage.{uF}) (T : F.TopologicalData) :
    LeftMixedProductDerivativeIso.{uF, uV} F T :=
  (leftMixedProductDerivative F T).1

/-- Every remaining valid order has a subsingleton carrier. -/
theorem leftMixedProductDerivativeVanishing
    (F : LocalFieldPackage.{uF}) (T : F.TopologicalData) :
    LeftMixedProductDerivativeVanishing.{uF, uV} F T :=
  (leftMixedProductDerivative F T).2

end Langlands.AllFieldBZ.Derivative
