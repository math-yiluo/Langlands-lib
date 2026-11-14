import Langlands.AllFieldBZ.Representation.Derivative.Homogeneity
import Langlands.AllFieldBZ.Representation.Mirabolic.MixedProducts
import Langlands.Representation.Derivative.LeftMixedProductHomogeneityStatement

/-!
# All-field port of `Langlands.Representation.Derivative.LeftMixedProductHomogeneityStatement`

Mechanical port of the field-dependent declarations of the p-adic module
`Langlands.Representation.Derivative.LeftMixedProductHomogeneityStatement` to an arbitrary nonarchimedean local field
(`Langlands.AllFieldBZ.LocalFieldPackage`). See the paired Markdown.
-/
noncomputable section
namespace Langlands.AllFieldBZ.Derivative
open Langlands.Derivative hiding HasNonzeroDerivative IsHomogeneous LeftMixedProductHomogeneity generalLinearDerivative generalLinearDerivativePositive generalLinearDerivativePositive_eq generalLinearDerivativePositive_obj generalLinearDerivative_of_pos generalLinearDerivative_succ generalLinearDerivative_succ_obj generalLinearDerivative_top_succ generalLinearDerivative_zero generalLinearRankCast generalLinearRankCast_refl generalLinearRankCast_symm_comp generalLinearRankCast_trans generalLinearRestriction generalLinearRestriction_map_apply generalLinearRestriction_map_toLinearMap hasNonzeroDerivative_iff isHomogeneous_of_subsingleton le_level_of_hasNonzeroDerivative level level_eq_iff level_eq_zero_iff level_eq_zero_of_subsingleton level_le mirabolicDerivative mirabolicDerivativeOfOrder mirabolicDerivativeOfOrder_eq mirabolicDerivativeOfOrder_obj mirabolicDerivativeOfOrder_obj_subsingleton mirabolicDerivativeOfOrder_one mirabolicDerivativeOfOrder_top mirabolicDerivative_eq mirabolicDerivative_obj_subsingleton mirabolicDerivative_succ mirabolicDerivative_zero mirabolicRankCast mirabolicRankCast_obj_subsingleton mirabolicRankCast_refl phiMinusIterate phiMinusIterate_obj_subsingleton phiMinusIterate_succ phiMinusIterate_zero
universe uF uV

variable (F : LocalFieldPackage.{uF}) (T : F.TopologicalData)

/-- For every representation `ρ` of `GL_k` and every homogeneous representation
`τ` of `P_(r+1)`, the actual left mixed product `ρ × τ` of `P_(k+r+1)` is
homogeneous. -/
def LeftMixedProductHomogeneity : Prop :=
  letI := T.topology
  ∀ (ψ : @HarmonicAnalysis.UnitaryAdditiveCharacter F.Carrier _ T.topology)
    (k r : ℕ) (ρ : SmoothRep.{0, uF, uV} ℂ (GeneralLinear k F.Carrier))
    (τ : SmoothRep.{0, uF, uV} ℂ (GeneralLinear.mirabolic r F.Carrier)),
    IsHomogeneous T ψ τ →
      IsHomogeneous T ψ ((T.leftMixedProductFunctor k r).obj (ρ, τ))

end Langlands.AllFieldBZ.Derivative
