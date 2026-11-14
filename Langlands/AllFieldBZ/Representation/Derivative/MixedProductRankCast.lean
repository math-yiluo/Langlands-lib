import Langlands.AllFieldBZ.Representation.Derivative.Homogeneity
import Langlands.AllFieldBZ.Representation.Mirabolic.MixedProducts
import Langlands.Representation.Derivative.MixedProductRankCast

/-!
# All-field port of `Langlands.Representation.Derivative.MixedProductRankCast`

Mechanical port of the field-dependent declarations of the p-adic module
`Langlands.Representation.Derivative.MixedProductRankCast` to an arbitrary nonarchimedean local field
(`Langlands.AllFieldBZ.LocalFieldPackage`). See the paired Markdown.
-/
noncomputable section
open CategoryTheory
namespace Langlands.AllFieldBZ.Derivative
open Langlands.Derivative hiding HasNonzeroDerivative IsHomogeneous generalLinearDerivative generalLinearDerivativePositive generalLinearDerivativePositive_eq generalLinearDerivativePositive_obj generalLinearDerivative_of_pos generalLinearDerivative_succ generalLinearDerivative_succ_obj generalLinearDerivative_top_succ generalLinearDerivative_zero generalLinearRankCast generalLinearRankCast_refl generalLinearRankCast_symm_comp generalLinearRankCast_trans generalLinearRestriction generalLinearRestriction_map_apply generalLinearRestriction_map_toLinearMap hasNonzeroDerivative_iff isHomogeneous_of_subsingleton le_level_of_hasNonzeroDerivative leftMixedProduct_rankCast level level_eq_iff level_eq_zero_iff level_eq_zero_of_subsingleton level_le mirabolicDerivative mirabolicDerivativeOfOrder mirabolicDerivativeOfOrder_eq mirabolicDerivativeOfOrder_obj mirabolicDerivativeOfOrder_obj_subsingleton mirabolicDerivativeOfOrder_one mirabolicDerivativeOfOrder_top mirabolicDerivative_eq mirabolicDerivative_obj_subsingleton mirabolicDerivative_succ mirabolicDerivative_zero mirabolicRankCast mirabolicRankCast_obj_subsingleton mirabolicRankCast_refl phiMinusIterate phiMinusIterate_obj_subsingleton phiMinusIterate_succ phiMinusIterate_zero
open Langlands.GeneralLinear
universe uF uV

variable {F : LocalFieldPackage.{uF}}

/-- Transport of the mirabolic input rank commutes with the actual left product. -/
theorem leftMixedProduct_rankCast (T : F.TopologicalData) (k : ℕ)
    {a b : ℕ} (h : a = b) :
    letI := T.topology
    (𝟭 (SmoothRep.{0, uF, uV} ℂ (GeneralLinear k F.Carrier))).prod
        (mirabolicRankCast T h) ⋙ T.leftMixedProductFunctor k b =
      T.leftMixedProductFunctor k a ⋙ mirabolicRankCast T (congrArg (k + ·) h) := by
  subst h
  exact (Functor.id_comp _).trans (Functor.comp_id _).symm

end Langlands.AllFieldBZ.Derivative
