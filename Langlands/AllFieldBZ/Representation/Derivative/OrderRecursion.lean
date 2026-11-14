import Langlands.AllFieldBZ.Representation.Derivative.Homogeneity
import Langlands.Representation.Derivative.OrderRecursion

/-!
# All-field port of `Langlands.Representation.Derivative.OrderRecursion`

Mechanical port of the field-dependent declarations of the p-adic module
`Langlands.Representation.Derivative.OrderRecursion` to an arbitrary nonarchimedean local field
(`Langlands.AllFieldBZ.LocalFieldPackage`). See the paired Markdown.
-/
noncomputable section
open CategoryTheory
namespace Langlands.AllFieldBZ.Derivative
open Langlands.Derivative hiding HasNonzeroDerivative IsHomogeneous generalLinearDerivative generalLinearDerivativePositive generalLinearDerivativePositive_eq generalLinearDerivativePositive_obj generalLinearDerivative_of_pos generalLinearDerivative_succ generalLinearDerivative_succ_obj generalLinearDerivative_top_succ generalLinearDerivative_zero generalLinearRankCast generalLinearRankCast_refl generalLinearRankCast_symm_comp generalLinearRankCast_trans generalLinearRestriction generalLinearRestriction_map_apply generalLinearRestriction_map_toLinearMap hasNonzeroDerivative_iff isHomogeneous_of_subsingleton le_level_of_hasNonzeroDerivative level level_eq_iff level_eq_zero_iff level_eq_zero_of_subsingleton level_le mirabolicDerivative mirabolicDerivativeOfOrder mirabolicDerivativeOfOrder_eq mirabolicDerivativeOfOrder_obj mirabolicDerivativeOfOrder_obj_subsingleton mirabolicDerivativeOfOrder_one mirabolicDerivativeOfOrder_top mirabolicDerivative_eq mirabolicDerivative_obj_subsingleton mirabolicDerivative_succ mirabolicDerivative_zero mirabolicRankCast mirabolicRankCast_obj_subsingleton mirabolicRankCast_refl mirabolicRankCast_symm_comp mirabolicRankCast_trans phiMinusIterate phiMinusIterate_obj_subsingleton phiMinusIterate_succ phiMinusIterate_zero phiMinus_rankCast
open Langlands.GeneralLinear
open Langlands.HarmonicAnalysis
universe uF uV

variable {F : LocalFieldPackage.{uF}}

theorem mirabolicRankCast_trans (T : F.TopologicalData) {a b c : ℕ}
    (h : a = b) (h' : b = c) :
    letI := T.topology
    mirabolicRankCast.{uF, uV} T h ⋙ mirabolicRankCast T h' =
      mirabolicRankCast T (h.trans h') := by
  subst h h'
  exact Functor.id_comp _

theorem mirabolicRankCast_symm_comp (T : F.TopologicalData) {a b : ℕ} (h : a = b) :
    letI := T.topology
    mirabolicRankCast.{uF, uV} T h ⋙ mirabolicRankCast T h.symm =
      𝟭 (SmoothRep.{0, uF, uV} ℂ (mirabolic a F.Carrier)) := by
  subst h
  exact Functor.id_comp _

theorem phiMinus_rankCast (T : F.TopologicalData)
    (ψ : @UnitaryAdditiveCharacter F.Carrier _ T.topology) {a b : ℕ} (h : a = b) :
    letI := T.topology
    mirabolicRankCast.{uF, uV} T (congrArg (· + 1) h) ⋙ Mirabolic.phiMinus T ψ b =
      Mirabolic.phiMinus T ψ a ⋙ mirabolicRankCast T h := by
  subst h
  exact (Functor.id_comp _).trans (Functor.comp_id _).symm

end Langlands.AllFieldBZ.Derivative
