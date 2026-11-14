import Langlands.AllFieldBZ.Representation.Derivative.LeftMixedProductDerivativeProof
import Langlands.AllFieldBZ.Representation.Derivative.LeftMixedProductHomogeneityStatement
import Langlands.AllFieldBZ.Representation.Derivative.LeftMixedProductPhiHatIterate
import Langlands.AllFieldBZ.Representation.Derivative.MirabolicDerivativeUnitInjective
import Langlands.AllFieldBZ.Representation.Derivative.RestrictedProductLevel
import Langlands.Representation.Derivative.LeftMixedProductHomogeneityProof

/-!
# All-field port of `Langlands.Representation.Derivative.LeftMixedProductHomogeneityProof`

Mechanical port of the field-dependent declarations of the p-adic module
`Langlands.Representation.Derivative.LeftMixedProductHomogeneityProof` to an arbitrary nonarchimedean local field
(`Langlands.AllFieldBZ.LocalFieldPackage`). See the paired Markdown.
-/
noncomputable section
namespace Langlands.AllFieldBZ.Derivative
open Langlands.Derivative hiding HasNonzeroDerivative IsHomogeneous LeftMixedProductDerivative LeftMixedProductDerivativeIso LeftMixedProductDerivativeVanishing LeftMixedProductHomogeneity MirabolicDerivativeDetection MirabolicProductMinusCompatibilityStatement MirabolicProductRestrictionStatement RightMixedProductPhiMinusDetection generalLinearDerivative generalLinearDerivativePositive generalLinearDerivativePositive_eq generalLinearDerivativePositive_obj generalLinearDerivative_of_pos generalLinearDerivative_succ generalLinearDerivative_succ_obj generalLinearDerivative_top_succ generalLinearDerivative_zero generalLinearRankCast generalLinearRankCast_refl generalLinearRankCast_symm_comp generalLinearRankCast_trans generalLinearRestriction generalLinearRestriction_map_apply generalLinearRestriction_map_toLinearMap hasNonzeroDerivative_iff hasNonzeroDerivative_of_isHomogeneous isHomogeneous_of_subsingleton le_level_of_hasNonzeroDerivative leftMixedProductDerivative leftMixedProductDerivativeIso leftMixedProductDerivativeVanishing leftMixedProductHomogeneity leftMixedProduct_rankCast level level_eq_iff level_eq_zero_iff level_eq_zero_of_subsingleton level_le mirabolicDerivative mirabolicDerivativeAdjunction mirabolicDerivativeAdjunction_comp_left mirabolicDerivativeDetection mirabolicDerivativeOfOrder mirabolicDerivativeOfOrderAdjunction mirabolicDerivativeOfOrderAdjunction_comp_left mirabolicDerivativeOfOrderAdjunction_unit mirabolicDerivativeOfOrderAdjunction_unit_comp mirabolicDerivativeOfOrderRightAdjoint mirabolicDerivativeOfOrderUnit mirabolicDerivativeOfOrderUnitKer mirabolicDerivativeOfOrderUnit_injective mirabolicDerivativeOfOrderUnit_injective_of_forall mirabolicDerivativeOfOrder_eq mirabolicDerivativeOfOrder_map_eq_zero_of_unit_comp mirabolicDerivativeOfOrder_map_injective mirabolicDerivativeOfOrder_obj mirabolicDerivativeOfOrder_obj_subsingleton mirabolicDerivativeOfOrder_one mirabolicDerivativeOfOrder_top mirabolicDerivativeRightAdjoint mirabolicDerivative_eq mirabolicDerivative_obj_subsingleton mirabolicDerivative_succ mirabolicDerivative_zero mirabolicRankCast mirabolicRankCastHomEquiv mirabolicRankCastHomEquiv_comp_left mirabolicRankCast_obj_subsingleton mirabolicRankCast_refl mirabolicRankCast_symm_comp mirabolicRankCast_trans phiHatPlusIterate phiHatPlusIterateAdjunction phiHatPlusIterateAdjunction_comp_left phiHatPlusIterateAdjunction_succ phiMinusIterate phiMinusIterate_obj_subsingleton phiMinusIterate_succ phiMinusIterate_zero phiMinus_rankCast subsingleton_mirabolicDerivativeOfOrder_unit_ker
open Langlands.GeneralLinear
open Langlands.AllFieldBZ.GeneralLinear
open Langlands.HarmonicAnalysis hiding PadicRectangularHaarScalingStatement padicRectangularHaarScaling padicRectangularHaarScalingStatement padicScalarHaarScaling
open Langlands.AllFieldBZ.HarmonicAnalysis
universe uF uV

/-- Zelevinsky 5.3: a left mixed product `ρ × τ` with homogeneous `τ` is homogeneous. -/
theorem leftMixedProductHomogeneity
    (F : LocalFieldPackage.{uF}) (T : F.TopologicalData) :
    LeftMixedProductHomogeneity.{uF, uV} F T := by
  let _ := T.topology
  intro ψ k r ρ τ hτ U hU
  have hsub : level T ψ (SmoothRep.subrepresentation ((T.leftMixedProductFunctor k r).obj (ρ, τ)) U)
      ≤ level T ψ ((T.leftMixedProductFunctor k r).obj (ρ, τ)) :=
    LevelCalculus.level_le_of_injective T ψ (Mirabolic.minusExactness.{uF, max uF uV} F T)
      (SmoothRep.subtype _ U) (SmoothRep.subtype_injective _ U)
  have htop : level T ψ ((T.leftMixedProductFunctor k r).obj (ρ, τ)) ≤ level T ψ τ :=
    RestrictedProductLevel.level_leftMixed_le T ψ
      (leftMixedProductDerivative.{uF, uV} F T) ρ τ
  rcases Nat.eq_zero_or_pos (level T ψ τ) with h0 | hpos
  · omega
  · have hl : 0 < level T ψ τ ∧ level T ψ τ ≤ r + 1 := ⟨hpos, level_le T ψ τ⟩
    have hβ := mirabolicDerivativeOfOrderUnit_injective T ψ r (level T ψ τ) hl τ hτ rfl
    have hlow := le_level_of_hasNonzeroDerivative T ψ _
      (Mirabolic.hasNonzeroDerivative_leftMixed_subrepresentation T ψ hl ρ τ _
        (mirabolicDerivativeOfOrderUnit T ψ r (level T ψ τ) hl τ) hβ U hU)
    omega

end Langlands.AllFieldBZ.Derivative
