import Langlands.Geometry.Building.UnramifiedTorusUnitFixedApartmentStatement
import Langlands.Geometry.Building.UnramifiedFixedPointTransporterStatement
import Langlands.Geometry.Building.UnramifiedTwistedFixedTranslationStatement
import Langlands.Geometry.Building.UnramifiedSplitTranslationFixerStatement
import Langlands.Geometry.Building.MaximalUnramifiedApartmentInjective
import Langlands.Geometry.Building.UnramifiedGaloisFixedApartmentProof
import Langlands.GroupScheme.Reductive.FieldExtensionProof

/-! # Reduction of KP Proposition 9.3.13 over `K` to three focused inputs -/

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry
open scoped CategoryTheory.MonObj
open Langlands.GroupScheme Langlands.GroupScheme.GaloisPointComparison
open Langlands.LocalGalois.Separable

namespace Langlands.Geometry.Building

/-- The split-centralizing transporter input, the twisted fixed-translation input and
the split-translation fixer input together imply the torus-unit fixed-apartment
statement (KP Proposition 9.3.13 over `K`). -/
def UnramifiedTorusUnitFixedApartmentReductionStatement : Prop :=
  UnramifiedFixedPointTransporterStatement.{u} →
    UnramifiedTwistedFixedTranslationStatement.{u} →
    UnramifiedSplitTranslationFixerStatement.{u} →
    UnramifiedTorusUnitFixedApartmentStatement.{u}

set_option maxHeartbeats 8000000 in
set_option synthInstance.maxHeartbeats 400000 in
/-- Proof of `UnramifiedTorusUnitFixedApartmentReductionStatement`. -/
theorem unramifiedTorusUnitFixedApartmentReduction :
    UnramifiedTorusUnitFixedApartmentReductionStatement.{u} := by
  intro hP1 hP2 hP3 F _ _ _ _ G hG S iS hiS T iT f hf
  let : IsAffineHom G.X.hom := hG.isAffineHom
  intro hiT
  have := mono_of_isMaximalSplitTorus hiT
  have : Mono ((GroupScheme.baseChange
      (algebraBaseMap F (inertiaFixedField F))).map iT).hom.hom.left :=
    mono_of_isMaximalSplitTorus hiT
  intro D C h6 hD y hy hyU
  have hGK : IsConnectedReductive (baseChanged F (inertiaFixedField F) G) :=
    connectedReductiveFieldExtensionStatement F (inertiaFixedField F) G hG
  have hinj : Function.Injective D.apartmentMap := D.apartmentMap_injective hGK hiT
  obtain ⟨x₀, hx₀⟩ := unramifiedGaloisFixedApartment F G hG T iT hiT D hD
  have hx₀' : ∀ σ : inertiaFixedField F ≃ₐ[F] inertiaFixedField F,
      KPApartmentData.galoisAction F (inertiaFixedField F) iT D hD σ x₀ = x₀ :=
    fun σ => KPApartmentData.Apartment.ext (by rw [KPApartmentData.galoisAction_val]; exact hx₀ σ)
  obtain ⟨h, hcomm, hfix₀, hN, x₁, rfl⟩ :=
    hP1 F G hG S iS hiS T iT f hf hiT D C h6 hD x₀ hx₀ y hy hyU
  let n : (inertiaFixedField F ≃ₐ[F] inertiaFixedField F) →
      normalizerPoints
        (T := (CommGroupScheme.baseChange (algebraBaseMap F (inertiaFixedField F))).obj T)
        ((GroupScheme.baseChange (algebraBaseMap F (inertiaFixedField F))).map iT) :=
    fun σ => ⟨_, hN σ⟩
  have hn : ∀ σ : inertiaFixedField F ≃ₐ[F] inertiaFixedField F,
      ((n σ : rationalPoints (baseChanged F (inertiaFixedField F) G))) =
        h⁻¹ * rationalConjugate F (inertiaFixedField F) G σ h := fun σ => rfl
  -- Coefficient-fixedness of `h • [x]` is the twisted fixedness `n σ • σ(x) = x`.
  have key := fun (x : D.Apartment) (σ : inertiaFixedField F ≃ₐ[F] inertiaFixedField F)
      (hx : KPApartmentData.galoisQuotientAction F (inertiaFixedField F) iT D hD σ
        (h • D.apartmentMap x) = h • D.apartmentMap x) =>
    have hx' : rationalConjugate F (inertiaFixedField F) G σ h •
        D.apartmentMap (KPApartmentData.galoisAction F (inertiaFixedField F) iT D hD σ x) =
          h • D.apartmentMap x := by
      rw [← KPApartmentData.galoisQuotientAction_apartmentMap,
        ← KPApartmentData.galoisQuotientAction_smul]
      exact hx
    hinj ((D.apartmentMap_smul (n σ)
        (KPApartmentData.galoisAction F (inertiaFixedField F) iT D hD σ x)).trans
      ((mul_smul h⁻¹ (rationalConjugate F (inertiaFixedField F) G σ h)
          (D.apartmentMap (KPApartmentData.galoisAction F (inertiaFixedField F) iT D hD σ x))).trans
        ((congrArg (h⁻¹ • ·) hx').trans (inv_smul_smul h (D.apartmentMap x)))))
  have t₀ := fun σ : inertiaFixedField F ≃ₐ[F] inertiaFixedField F => by
    have h₀ := key x₀ σ (by
      rw [hfix₀, KPApartmentData.galoisQuotientAction_apartmentMap, hx₀' σ])
    rw [hx₀' σ] at h₀
    exact h₀
  have t₁ := fun σ => key x₁ σ (hy σ)
  -- The difference `x₁ - x₀` is fixed by every twisted coefficient map.
  have hv : ∀ σ : inertiaFixedField F ≃ₐ[F] inertiaFixedField F,
      translationAction
          (S := (CommGroupScheme.baseChange (algebraBaseMap F (inertiaFixedField F))).obj T)
          ((GroupScheme.baseChange (algebraBaseMap F (inertiaFixedField F))).map iT) (n σ)
        (galoisTranslationAction F (inertiaFixedField F) iT σ (x₁ -ᵥ x₀)) = x₁ -ᵥ x₀ := by
    intro σ
    have e := t₁ σ
    rw [← vsub_vadd x₁ x₀, KPApartmentData.galoisAction_vadd, hx₀' σ,
      KPApartmentData.smul_vadd, t₀ σ] at e
    exact vadd_right_cancel x₀ e
  have hmem := hP2 F G hG S iS hiS T iT f hf hiT h hcomm n hn (x₁ -ᵥ x₀) hv
  have hfix₁ := hP3 F G hG S iS hiS T iT f hf hiT D C h6 h hcomm x₀ hfix₀ (x₁ -ᵥ x₀) hmem
  rw [vsub_vadd] at hfix₁
  refine ⟨x₁, fun σ => ?_, hfix₁.symm⟩
  have hσ := hy σ
  rw [hfix₁, KPApartmentData.galoisQuotientAction_apartmentMap] at hσ
  exact congrArg KPApartmentData.Apartment.val (hinj hσ)

end Langlands.Geometry.Building
