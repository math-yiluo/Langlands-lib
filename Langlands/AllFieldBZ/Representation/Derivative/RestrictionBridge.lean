import Langlands.AllFieldBZ.Representation.Derivative.LevelCalculus
import Langlands.Representation.Derivative.RestrictionBridge

/-!
# All-field port of `Langlands.Representation.Derivative.RestrictionBridge`

Mechanical port of the field-dependent declarations of the p-adic module
`Langlands.Representation.Derivative.RestrictionBridge` to an arbitrary nonarchimedean local field
(`Langlands.AllFieldBZ.LocalFieldPackage`). See the paired Markdown.
-/
noncomputable section
open CategoryTheory
namespace Langlands.AllFieldBZ.Derivative
open Langlands.Derivative hiding HasNonzeroDerivative IsHomogeneous MirabolicDerivativeDetection generalLinearDerivative generalLinearDerivativePositive generalLinearDerivativePositive_eq generalLinearDerivativePositive_obj generalLinearDerivative_of_pos generalLinearDerivative_succ generalLinearDerivative_succ_obj generalLinearDerivative_top_succ generalLinearDerivative_zero generalLinearRankCast generalLinearRankCast_refl generalLinearRankCast_symm_comp generalLinearRankCast_trans generalLinearRestriction generalLinearRestriction_map_apply generalLinearRestriction_map_toLinearMap hasNonzeroDerivative_iff isHomogeneous_of_subsingleton le_level_of_hasNonzeroDerivative level level_eq_iff level_eq_zero_iff level_eq_zero_of_subsingleton level_le mirabolicDerivative mirabolicDerivativeDetection mirabolicDerivativeOfOrder mirabolicDerivativeOfOrder_eq mirabolicDerivativeOfOrder_obj mirabolicDerivativeOfOrder_obj_subsingleton mirabolicDerivativeOfOrder_one mirabolicDerivativeOfOrder_top mirabolicDerivative_eq mirabolicDerivative_obj_subsingleton mirabolicDerivative_succ mirabolicDerivative_zero mirabolicRankCast mirabolicRankCast_obj_subsingleton mirabolicRankCast_refl phiMinusIterate phiMinusIterate_obj_subsingleton phiMinusIterate_succ phiMinusIterate_zero
open Langlands.GeneralLinear
open Langlands.HarmonicAnalysis hiding PadicRectangularHaarScalingStatement padicScalarHaarScaling
open Langlands.AllFieldBZ.HarmonicAnalysis
universe uF uV

variable {F : LocalFieldPackage.{uF}}

namespace RestrictionBridge
open Langlands.Derivative.RestrictionBridge hiding generalLinearDerivative_succ_obj_eq generalLinearRestriction_rankCast_obj isHomogeneous_of_single_order nontrivial_generalLinearRankCast_iff
open Langlands.Derivative.LevelCalculus hiding hasNonzeroDerivative_iff_of_iso hasNonzeroDerivative_level hasNonzeroDerivative_of_injective hasNonzeroDerivative_succ_iff hasNonzeroDerivative_succ_iff_cast isHomogeneous_of_forall_injective isHomogeneous_of_iso level_eq_level_phiMinus_succ level_eq_of_isHomogeneous level_eq_of_iso level_le_level_phiMinus_succ level_le_max_of_isShortExact level_le_of_imp level_le_of_injective level_le_one_of_subsingleton_phiMinus level_mirabolicRankCast level_pos mapsShortExact_mirabolicDerivative mapsShortExact_mirabolicDerivativeOfOrder mapsShortExact_mirabolicRankCast mapsShortExact_phiMinusIterate mirabolicDerivative_succ_cast_obj nontrivial_mirabolicDerivative_cast_congr nontrivial_of_hasNonzeroDerivative nontrivial_phiMinus_iff
open Langlands.AllFieldBZ.Derivative.LevelCalculus
variable (T : F.TopologicalData) (ψ : @UnitaryAdditiveCharacter F.Carrier _ T.topology)

/-- Restriction after a rank transport is the transported restriction. -/
theorem generalLinearRestriction_rankCast_obj {n c : ℕ} (e : n + 1 = c + 1) (e' : n = c) :
    letI := T.topology
    ∀ A : SmoothRep.{0, uF, uV} ℂ (GeneralLinear (n + 1) F.Carrier),
      (generalLinearRestriction T c).obj ((generalLinearRankCast T e).obj A) =
        (mirabolicRankCast T e').obj ((generalLinearRestriction T n).obj A) := by
  subst e'
  intro A
  rfl

/-- The positive-order `GL` derivative is the mirabolic derivative of the
restriction, with no further transport. -/
theorem generalLinearDerivative_succ_obj_eq {n j : ℕ} (hk : j + 1 ≤ n + 1)
    (hk' : 0 < j + 1 ∧ j + 1 ≤ n + 1) :
    letI := T.topology
    ∀ A : SmoothRep.{0, uF, uV} ℂ (GeneralLinear (n + 1) F.Carrier),
      (generalLinearDerivative T ψ (n + 1) (j + 1) hk).obj A =
        (mirabolicDerivativeOfOrder T ψ n (j + 1) hk').obj
          ((generalLinearRestriction T n).obj A) := by
  intro A
  rw [generalLinearDerivative_succ_obj, generalLinearDerivativePositive_obj,
    mirabolicDerivativeOfOrder_obj,
    generalLinearRestriction_rankCast_obj T (rank_eq_of_succ_le hk) (by omega)]
  rfl

theorem nontrivial_generalLinearRankCast_iff {a b : ℕ} (h : a = b) :
    letI := T.topology
    ∀ A : SmoothRep.{0, uF, uV} ℂ (GeneralLinear a F.Carrier),
      Nontrivial ((generalLinearRankCast T h).obj A) ↔ Nontrivial A := by
  subst h
  intro A
  rfl

section Single
variable (hE : Mirabolic.MinusExactnessStatement.{uF, uV} F T)
include hE

/-- A mirabolic representation whose nonzero derivatives all have one order
`c` is homogeneous: every nonzero subrepresentation has a nonzero derivative
(detection), of an order that is nonzero for the whole representation
(exactness). -/
theorem isHomogeneous_of_single_order {N : ℕ} (c : ℕ) :
    letI := T.topology
    ∀ A : SmoothRep.{0, uF, uV} ℂ (mirabolic N F.Carrier),
      (∀ j, HasNonzeroDerivative T ψ A j → j = c) → IsHomogeneous T ψ A := by
  intro A hA
  apply Langlands.AllFieldBZ.Derivative.LevelCalculus.isHomogeneous_of_forall_injective T ψ A c
  intro W f hf hW
  exact hA _ (Langlands.AllFieldBZ.Derivative.LevelCalculus.hasNonzeroDerivative_of_injective T ψ hE f hf _
    (Langlands.AllFieldBZ.Derivative.LevelCalculus.hasNonzeroDerivative_level T ψ W (Langlands.AllFieldBZ.Derivative.LevelCalculus.level_pos T ψ W).ne'))

end Single
end RestrictionBridge
end Langlands.AllFieldBZ.Derivative
