import Langlands.Automorphic.WeakInductionAssociationReduction
import Langlands.Correspondence.UnramifiedReciprocityBridge
import Mathlib.Analysis.Complex.Polynomial.Basic

/-!
# Local characters that agree on units up to an unramified twist

Let `E'_u / F_v` be the completions at places `u | v` of number fields. A modulus-one
character `ψ` of `E'_uˣ` that agrees on units with the field character of a modulus-one
Weil character `η'` of `W_{E'_u}` has Weil character `η'` times the restriction of an
unramified modulus-one character of `W_{F_v}`.
-/

noncomputable section

set_option autoImplicit false

namespace Langlands.Global

open Langlands.Global.CompletionPadic Langlands.ClassField.Global

variable {F E' : Type} [Field F] [NumberField F] [Field E'] [NumberField E'] [Algebra F E']
  (v : FinitePlace F) (u : FinitePlace E') [u.asIdeal.LiesOver v.asIdeal]

/-- If `ψ` agrees on the units of `E'_u` with the field character of `η'`, then the Weil
character of `ψ` is `η'` times the restriction to `W_{E'_u}` of an unramified modulus-one
character of `W_{F_v}`. -/
theorem exists_weilCharacter_eq_mul_unramified
    (eu : LocalFactor.RankOne.ReciprocityCandidate (towerPadicField v u))
    (heu : LocalClassField.GeometricWeilReciprocityRelation (towerPadicField v u)
      (towerPadicField v u).canonicalTopologicalData eu)
    (η' : Weil.Local.localWeilGroup (towerPadicField v u) →ₜ* ℂˣ)
    (hη' : ∀ w, ‖(η' w : ℂ)‖ = 1)
    (ψ : (u.adicCompletion E')ˣ →ₜ* ℂˣ) (hψ : ∀ a, ‖(ψ a : ℂ)‖ = 1)
    (hunr : ∀ a : (u.adicCompletion E')ˣ, Valued.v (a : u.adicCompletion E') = 1 →
      ψ a = LocalFactor.RankOne.fieldCharacter (towerPadicField v u) eu η' a) :
    ∃ z : ℂˣ, ‖(z : ℂ)‖ = 1 ∧
      LocalFactor.RankOne.weilCharacter (towerPadicField v u) eu
          (quasicharacterAt u (residuePrime_eq v u) ψ) =
        η' * (Weil.Local.localUnramifiedCharacter (padicField v) z).comp
          (RelativeWeilGroup.completionWeilMap v u) := by
  let T := (towerPadicField v u).canonicalTopologicalData
  let θ := LocalFactor.RankOne.fieldCharacter (towerPadicField v u) eu η'
  let ψ' := quasicharacterAt u (residuePrime_eq v u) ψ
  let μ := ψ' * θ⁻¹
  have hμ1 : ∀ a : (towerPadicField v u).Carrierˣ, a ∈ T.ordUnits.ker → μ a = 1 := by
    intro a ha
    change Multiplicative.ofAdd (T.ord (a : u.adicCompletion E')) = 1 at ha
    rw [ofAdd_eq_one, PadicField.TopologicalData.ord,
      discreteValuation_padicFieldAt u (residuePrime_eq v u), neg_eq_zero] at ha
    have hne : Valued.v (a : u.adicCompletion E') ≠ 0 :=
      (Valuation.ne_zero_iff _).mpr a.ne_zero
    have hv : Valued.v (a : u.adicCompletion E') = 1 := by
      rw [← WithZero.exp_log hne, ha, WithZero.exp_zero]
    change ψ a * (θ a)⁻¹ = 1
    rw [hunr a hv, mul_inv_cancel]
  have hψθ : ψ' = θ * μ := by
    simp only [μ]
    rw [mul_comm ψ', ← mul_assoc, mul_inv_cancel, one_mul]
  have hw : LocalFactor.RankOne.weilCharacter (towerPadicField v u) eu ψ' =
      η' * LocalFactor.RankOne.weilCharacter (towerPadicField v u) eu μ := by
    rw [hψθ, ← LocalFactor.RankOne.weilCharacter_fieldCharacter (towerPadicField v u) eu η']
    rfl
  have hμ : LocalFactor.RankOne.weilCharacter (towerPadicField v u) eu μ =
      Weil.Local.localUnramifiedCharacter (towerPadicField v u)
        (μ T.uniformizerUnit) := by
    apply ContinuousMonoidHom.toMonoidHom_injective
    exact Correspondence.weilCharacter_eq_localUnramifiedCharacter (towerPadicField v u) heu
      (χ := μ) (by
        rw [PadicField.TopologicalData.IsUnramifiedCharacter,
          ← PadicField.TopologicalData.ker_ordUnits]
        exact fun a ha => hμ1 a ha)
  set t := μ T.uniformizerUnit with ht
  have htn : ‖(t : ℂ)‖ = 1 := by
    have h1 := congrArg (fun χ => χ (Weil.Local.localGeometricFrobenius (towerPadicField v u))) hw
    simp only [ContinuousMonoidHom.mul_apply, hμ,
      Weil.Local.localUnramifiedCharacter_geometricFrobenius] at h1
    have h2 : ‖((LocalFactor.RankOne.weilCharacter (towerPadicField v u) eu ψ'
        (Weil.Local.localGeometricFrobenius (towerPadicField v u)) : ℂˣ) : ℂ)‖ = 1 := hψ _
    rw [h1, Units.val_mul, norm_mul, hη', one_mul] at h2
    exact h2
  set f := Weil.Local.extensionResidueDegree (padicField v) (towerPadicField v u)
    (RelativeWeilGroup.completionPadicAlgHom v u)
  have hf : 0 < f := Weil.Local.extensionResidueDegree_pos _ _ _
  obtain ⟨z, hz⟩ := IsAlgClosed.exists_pow_nat_eq (t : ℂ) hf
  have hz0 : z ≠ 0 := by
    rintro rfl
    rw [zero_pow hf.ne'] at hz
    exact t.ne_zero hz.symm
  have hzn : ‖z‖ = 1 := by
    have : ‖z‖ ^ f = 1 := by rw [← norm_pow, hz, htn]
    exact (pow_eq_one_iff_of_nonneg (norm_nonneg z) hf.ne').mp this
  refine ⟨Units.mk0 z hz0, hzn, ?_⟩
  change LocalFactor.RankOne.weilCharacter (towerPadicField v u) eu ψ' = _
  rw [hw, hμ]
  congr 1
  ext w
  change ((Weil.Local.localUnramifiedCharacter (towerPadicField v u) t w : ℂˣ) : ℂ) =
    (Weil.Local.localUnramifiedCharacter (padicField v) (Units.mk0 z hz0)
      (RelativeWeilGroup.completionWeilMap v u w) : ℂˣ)
  rw [Weil.Local.localUnramifiedCharacter_extensionWeilMap]
  congr 3
  apply Units.ext
  simpa using hz.symm

end Langlands.Global
