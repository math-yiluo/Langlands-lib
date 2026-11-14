import Langlands.AllFieldBZ.Representation.Derivative.TopLocalizationComparison
import Langlands.Representation.Whittaker.TopDerivativeDual

/-!
# All-field port of `Langlands.Representation.Whittaker.TopDerivativeDual`

Mechanical port of the field-dependent declarations of the p-adic module
`Langlands.Representation.Whittaker.TopDerivativeDual` to an arbitrary nonarchimedean local field
(`Langlands.AllFieldBZ.LocalFieldPackage`). See the paired Markdown.
-/
noncomputable section
set_option backward.isDefEq.respectTransparency.types false

namespace Langlands.AllFieldBZ.Whittaker
open Langlands.Whittaker hiding functionalsTopDerivativeDualEquiv glFunctionalsTopDerivativeDualEquiv hasFunctional_iff_nontrivial_topDerivative hasStandardFunctional_iff_nontrivial_topDerivative
open CategoryTheory
open Langlands.GeneralLinear
open Langlands.Derivative hiding generalLinearDerivative generalLinearDerivativePositive generalLinearDerivativePositive_eq generalLinearDerivativePositive_obj generalLinearDerivative_of_pos generalLinearDerivative_succ generalLinearDerivative_succ_obj generalLinearDerivative_top_succ generalLinearDerivative_zero generalLinearRankCast generalLinearRankCast_refl generalLinearRankCast_symm_comp generalLinearRankCast_trans generalLinearRestriction generalLinearRestriction_map_apply generalLinearRestriction_map_toLinearMap mirabolicDerivative mirabolicDerivative_eq mirabolicDerivative_succ mirabolicDerivative_zero partialDerivative partialDerivativeMk partialDerivativeMk_surjective partialDerivativeMk_unipotent partialDerivative_action_mk partialDerivative_map_mk phiMinusIterate phiMinusIterate_succ phiMinusIterate_zero topDerivative topDerivative_eq topDerivative_zero
open Langlands.AllFieldBZ.Derivative
universe uF uV

section Algebraic
variable {R G V : Type*} [CommRing R] [Group G] [AddCommGroup V] [Module R V]

end Algebraic
variable {F : LocalFieldPackage.{uF}}
  (T : F.TopologicalData)
  (ψ : @HarmonicAnalysis.UnitaryAdditiveCharacter F.Carrier _ T.topology)

private def _root_.Langlands.Whittaker.rankCastLinearEquiv {a b : ℕ} (h : a = b)
    (X : letI := T.topology; SmoothRep.{0,uF,uV} ℂ (GeneralLinear a F.Carrier)) :
    letI := T.topology
    X ≃ₗ[ℂ] (Langlands.AllFieldBZ.Derivative.generalLinearRankCast T h).obj X := by
  subst b
  exact LinearEquiv.refl ℂ X

/-- In every rank, the entire space of equivariant functionals for the actual
upper-unipotent character is the algebraic dual of the entire top derivative. -/
def functionalsTopDerivativeDualEquiv (n : ℕ)
    (π : letI := T.topology;
      SmoothRep.{0,uF,uV} ℂ (GeneralLinear n F.Carrier)) :
    letI := T.topology
    functionals (upperUnipotent n F.Carrier) (entrywiseCharacter ψ.complex n)
      π.representation ≃ₗ[ℂ]
        Module.Dual ℂ ((Langlands.AllFieldBZ.Derivative.generalLinearDerivative T ψ n n le_rfl).obj π) := by
  letI := T.topology
  let e := (SmoothRep.equivOfIso
    ((Langlands.AllFieldBZ.Derivative.TopLocalization.topLocalizationIso T ψ n).app π)).toLinearEquiv
  let r := rankCastLinearEquiv T (Nat.sub_self n)
    ((Langlands.AllFieldBZ.Derivative.generalLinearDerivative T ψ n n le_rfl).obj π)
  exact (functionalsLocalizationDualEquiv _ _ π.representation).trans
    (e.trans r.symm).symm.dualMap

/-- The all-rank character has a nonzero functional exactly when the actual
whole top derivative is nonzero. This includes rank zero. -/
theorem hasFunctional_iff_nontrivial_topDerivative (n : ℕ)
    (π : letI := T.topology;
      SmoothRep.{0,uF,uV} ℂ (GeneralLinear n F.Carrier)) :
    letI := T.topology
    HasFunctional (N := upperUnipotent n F.Carrier)
      (θ := entrywiseCharacter ψ.complex n) π.representation ↔
        Nontrivial ((Langlands.AllFieldBZ.Derivative.generalLinearDerivative T ψ n n le_rfl).obj π) := by
  let := T.topology
  exact (hasFunctional_iff_nontrivial _ _ π.representation).trans
    ((Equiv.nontrivial_congr (functionalsTopDerivativeDualEquiv T ψ n π).toEquiv).trans
      (Module.nontrivial_dual_iff ℂ))

/-- The positive-rank specialization uses exactly the published standard
Whittaker character, including rank one. -/
def glFunctionalsTopDerivativeDualEquiv (n : ℕ)
    (π : letI := T.topology;
      SmoothRep.{0,uF,uV} ℂ (GeneralLinear (n + 1) F.Carrier)) :
    letI := T.topology
    glFunctionals ψ n π.representation ≃ₗ[ℂ]
      Module.Dual ℂ
        ((Langlands.AllFieldBZ.Derivative.generalLinearDerivative T ψ (n + 1) (n + 1) le_rfl).obj π) := by
  letI := T.topology
  rw [glFunctionals, ← entrywiseCharacter_eq_standardCharacter]
  exact functionalsTopDerivativeDualEquiv T ψ (n + 1) π

/-- Standard Whittaker nondegeneracy is nonvanishing of the whole top derivative. -/
theorem hasStandardFunctional_iff_nontrivial_topDerivative (n : ℕ)
    (π : letI := T.topology;
      SmoothRep.{0,uF,uV} ℂ (GeneralLinear (n + 1) F.Carrier)) :
    letI := T.topology
    HasFunctional (N := upperUnipotent (n + 1) F.Carrier)
      (θ := standardCharacter ψ n) π.representation ↔
        Nontrivial ((Langlands.AllFieldBZ.Derivative.generalLinearDerivative T ψ (n + 1) (n + 1) le_rfl).obj π) := by
  let := T.topology
  rw [← entrywiseCharacter_eq_standardCharacter]
  exact hasFunctional_iff_nontrivial_topDerivative T ψ (n + 1) π

end Langlands.AllFieldBZ.Whittaker
