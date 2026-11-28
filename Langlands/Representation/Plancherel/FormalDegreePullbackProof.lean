import Langlands.Representation.Plancherel.FormalDegreePullback
import Langlands.Representation.Smooth.Transfer.GroupEquivalence

/-! # Schur formal degree under exact quotient Haar transport -/

noncomputable section

universe uG uH uV

open MeasureTheory

namespace Langlands.Plancherel

open Langlands.HarishChandraSchwartz

/-- Pullback through a continuous group isomorphism preserves the Schur
formal degree under exact transport of the central quotient Haar. -/
theorem representationFormalDegree_pullback :
    RepresentationFormalDegreePullbackStatement.{uG, uH, uV} := by
  intro G _ _ _ H _ _ _ e A _ hA B _ hB hAB _ _ _ _ μG _ _ μH _ _ hμ hcofG hcofH
    V _ _ ρ hρ hiρ hσ hiσ
  let cG := Classical.choose hρ.2
  let cH := Classical.choose hσ.2
  let hG : ∀ (a : A) (v : V), ρ a v =
      ((cG.character.comp (Subgroup.inclusion hA)) a : ℂ) • v :=
    fun a v => cG.acts (Subgroup.inclusion hA a) v
  let hH : ∀ (b : B) (v : V), (ρ.comp e.toMonoidHom) b v =
      ((cH.character.comp (Subgroup.inclusion hB)) b : ℂ) • v :=
    fun b v => cH.acts (Subgroup.inclusion hB b) v
  refine formalDegree_unique A hA μG hG hcofG hρ hiρ
    (orthogonalityIntegral_eq_representationFormalDegree A hA μG hcofG hG hρ hiρ) ?_
  intro v₁ ℓ₁ v₂ ℓ₂
  let ℓ₁H : SmoothDual (ρ.comp e.toMonoidHom) :=
    ⟨ℓ₁.val, (isSmoothVector_dual_comp_continuousMulEquiv_iff ρ e ℓ₁.val).mpr ℓ₁.property⟩
  let ℓ₂H : SmoothDual (ρ.comp e.toMonoidHom) :=
    ⟨ℓ₂.val, (isSmoothVector_dual_comp_continuousMulEquiv_iff ρ e ℓ₂.val).mpr ℓ₂.property⟩
  have hIntegrand :
      orthogonalityIntegrand B hH hH v₁ ℓ₁H.val v₂ ℓ₂H.val =
        orthogonalityIntegrand A hG hG v₁ ℓ₁.val v₂ ℓ₂.val ∘
          quotientContinuousMulEquiv e A B hAB := by
    funext q
    obtain ⟨h, rfl⟩ := QuotientGroup.mk_surjective q
    rw [Function.comp_apply, quotientContinuousMulEquiv_mk,
      orthogonalityIntegrand_mk, orthogonalityIntegrand_mk]
    change ℓ₁.val (ρ (e h) v₁) * ℓ₂.val (ρ (e h⁻¹) v₂) =
      ℓ₁.val (ρ (e h) v₁) * ℓ₂.val (ρ ((e h)⁻¹) v₂)
    rw [map_inv e]
  calc
    _ = orthogonalityIntegral B μH hH hH v₁ ℓ₁H v₂ ℓ₂H := by
      unfold orthogonalityIntegral
      rw [hIntegrand, ← hμ]
      exact integral_map_equiv
        (quotientContinuousMulEquiv e A B hAB).toHomeomorph.toMeasurableEquiv _
    _ = _ :=
      orthogonalityIntegral_eq_representationFormalDegree B hB μH hcofH hH hσ hiσ
        v₁ ℓ₁H v₂ ℓ₂H

end Langlands.Plancherel
