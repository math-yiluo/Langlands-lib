import Langlands.Representation.Derivative.TopLocalizationComparison
import Langlands.Representation.Whittaker.LocalizationDual

/-! # Full Whittaker functionals and the dual of the top derivative -/

noncomputable section

set_option backward.isDefEq.respectTransparency.types false

namespace Langlands.Whittaker

open CategoryTheory GeneralLinear Derivative

universe uF uV

section Algebraic

variable {R G V : Type*} [CommRing R] [Group G] [AddCommGroup V] [Module R V]

/-- A nonzero equivariant functional exists exactly when the whole functional
space is nontrivial. -/
theorem hasFunctional_iff_nontrivial (N : Subgroup G) (θ : N →* Rˣ)
    (ρ : Representation R G V) :
    HasFunctional (N := N) (θ := θ) ρ ↔ Nontrivial (functionals N θ ρ) := by
  constructor
  · rintro ⟨ℓ, hℓ⟩
    exact nontrivial_of_ne ℓ 0 (fun h => hℓ (congrArg Subtype.val h))
  · intro h
    let := h
    obtain ⟨ℓ, hℓ⟩ := exists_ne (0 : functionals N θ ρ)
    exact ⟨ℓ, fun hzero => hℓ (Subtype.ext hzero)⟩

end Algebraic

variable {p : ℕ} [Fact p.Prime] {F : PadicField.{uF} p}
  (T : F.TopologicalData)
  (ψ : @HarmonicAnalysis.UnitaryAdditiveCharacter F.Carrier _ T.topology)

private def rankCastLinearEquiv {a b : ℕ} (h : a = b)
    (X : letI := T.topology; SmoothRep.{0,uF,uV} ℂ (GeneralLinear a F.Carrier)) :
    letI := T.topology
    X ≃ₗ[ℂ] (generalLinearRankCast T h).obj X := by
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
        Module.Dual ℂ ((generalLinearDerivative T ψ n n le_rfl).obj π) := by
  letI := T.topology
  let e := (SmoothRep.equivOfIso
    ((TopLocalization.topLocalizationIso T ψ n).app π)).toLinearEquiv
  let r := rankCastLinearEquiv T (Nat.sub_self n)
    ((generalLinearDerivative T ψ n n le_rfl).obj π)
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
        Nontrivial ((generalLinearDerivative T ψ n n le_rfl).obj π) := by
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
        ((generalLinearDerivative T ψ (n + 1) (n + 1) le_rfl).obj π) := by
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
        Nontrivial ((generalLinearDerivative T ψ (n + 1) (n + 1) le_rfl).obj π) := by
  let := T.topology
  rw [← entrywiseCharacter_eq_standardCharacter]
  exact hasFunctional_iff_nontrivial_topDerivative T ψ (n + 1) π

end Langlands.Whittaker
