import Langlands.Representation.Archimedean.RealMixedSwapLie
import Langlands.Representation.Archimedean.RealUnlinkedSwapReduction

/-! # Conjugating real rank-three intertwiners by signed reversal -/

noncomputable section

open scoped Matrix Matrix.Norms.Operator Manifold ContDiff TensorProduct

namespace Langlands.Archimedean.RealMixedSwapTwist

open Langlands.LocalFactor.Archimedean

attribute [local instance 100] LieRing.ofAssociativeRing

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

/-- Conjugation of a linear map between reversed modules. -/
def conjugateMap {ds es ds' es' : List RealBlock}
    (e₁ : kFiniteFunctions (realStandardModule 3 ds) (unitaryCompact ℝ 3) ≃ₗ[ℂ]
      kFiniteFunctions (realStandardModule 3 ds') (unitaryCompact ℝ 3))
    (e₂ : kFiniteFunctions (realStandardModule 3 es) (unitaryCompact ℝ 3) ≃ₗ[ℂ]
      kFiniteFunctions (realStandardModule 3 es') (unitaryCompact ℝ 3))
    (T : kFiniteFunctions (realStandardModule 3 ds') (unitaryCompact ℝ 3) →ₗ[ℂ]
      kFiniteFunctions (realStandardModule 3 es') (unitaryCompact ℝ 3)) :
    kFiniteFunctions (realStandardModule 3 ds) (unitaryCompact ℝ 3) →ₗ[ℂ]
      kFiniteFunctions (realStandardModule 3 es) (unitaryCompact ℝ 3) :=
  e₂.symm.toLinearMap ∘ₗ T ∘ₗ e₁.toLinearMap

/-- Signed reversal carries the compact action to its common sign-character twist. -/
theorem signedEquiv_map_rep (q : ℕ) {ds ds' : List RealBlock}
    (e : kFiniteFunctions (realStandardModule 3 ds) (unitaryCompact ℝ 3) ≃ₗ[ℂ]
      kFiniteFunctions (realStandardModule 3 ds') (unitaryCompact ℝ 3))
    (he : ∀ f, (e f : G → ℂ) = signedTwistLin q f)
    (k : Matrix.unitaryGroup (Fin 3) ℝ)
    (f : kFiniteFunctions (realStandardModule 3 ds) (unitaryCompact ℝ 3)) :
    e (realStandardRep 3 ds k f) =
      signDet (Unitary.toUnits k) ^ q • realStandardRep 3 ds' k (e f) := by
  apply Subtype.ext
  simp only [he, realStandardRep_apply_coe, Submodule.coe_smul]
  rw [rightTranslation_signedTwistLin q (f : G → ℂ)
    (⟨Unitary.toUnits k, k.2⟩ : unitaryCompact ℝ 3)]
  rw [smul_smul, ← sq, ← pow_mul, Nat.mul_comm q 2, pow_mul, signDet_sq,
    one_pow, one_smul]

/-- Signed reversal carries the infinitesimal action through inverse transpose. -/
theorem signedEquiv_map_lie (q : ℕ) {ds ds' : List RealBlock}
    (e : kFiniteFunctions (realStandardModule 3 ds) (unitaryCompact ℝ 3) ≃ₗ[ℂ]
      kFiniteFunctions (realStandardModule 3 ds') (unitaryCompact ℝ 3))
    (he : ∀ f, (e f : G → ℂ) = signedTwistLin q f)
    (X : A) (f : kFiniteFunctions (realStandardModule 3 ds) (unitaryCompact ℝ 3)) :
    e (realStandardLie 3 ds (1 ⊗ₜ X) f) =
      realStandardLie 3 ds' (1 ⊗ₜ reverseDirection X) (e f) := by
  apply Subtype.ext
  simp only [he, realStandardLie_one_tmul_apply_coe]
  exact signedTwistLin_rightDerivative q (contMDiff_of_mem_realStandardModule f.2.1) X

/-- Conjugating by the same signed reversal preserves the intertwining property. -/
theorem isRealStandardIntertwiner_conjugateMap (q : ℕ)
    {ds es ds' es' : List RealBlock}
    (e₁ : kFiniteFunctions (realStandardModule 3 ds) (unitaryCompact ℝ 3) ≃ₗ[ℂ]
      kFiniteFunctions (realStandardModule 3 ds') (unitaryCompact ℝ 3))
    (e₂ : kFiniteFunctions (realStandardModule 3 es) (unitaryCompact ℝ 3) ≃ₗ[ℂ]
      kFiniteFunctions (realStandardModule 3 es') (unitaryCompact ℝ 3))
    (he₁ : ∀ f, (e₁ f : G → ℂ) = signedTwistLin q f)
    (he₂ : ∀ f, (e₂ f : G → ℂ) = signedTwistLin q f)
    {T : kFiniteFunctions (realStandardModule 3 ds') (unitaryCompact ℝ 3) →ₗ[ℂ]
      kFiniteFunctions (realStandardModule 3 es') (unitaryCompact ℝ 3)}
    (hT : IsRealStandardIntertwiner 3 (realStandardRep 3 es') (realStandardLie 3 es') ds' T) :
    IsRealStandardIntertwiner 3 (realStandardRep 3 es) (realStandardLie 3 es) ds
      (conjugateMap e₁ e₂ T) := by
  refine ⟨fun k f =>
    ⟨rightTranslation_mem_kFiniteFunctions_realStandardModule 3 ds f.2 k.2, ?_⟩,
    fun X f => ⟨rightDerivative_mem_kFiniteFunctions_realStandardModule 3 ds f.2 X, ?_⟩⟩
  · let ku : Matrix.unitaryGroup (Fin 3) ℝ := ⟨(k : G).val, k.2⟩
    have hk : Unitary.toUnits ku = (k : G) := Units.ext rfl
    have hsrc : (⟨Whittaker.rightTranslation ℂ G (k : G) (f : G → ℂ),
        rightTranslation_mem_kFiniteFunctions_realStandardModule 3 ds f.2 k.2⟩ :
        kFiniteFunctions (realStandardModule 3 ds) (unitaryCompact ℝ 3)) =
        realStandardRep 3 ds ku f := by
      apply Subtype.ext
      rw [realStandardRep_apply_coe, hk]
    change e₂.symm (T (e₁ _)) = realStandardRep 3 es ku (e₂.symm (T (e₁ f)))
    rw [hsrc]
    apply e₂.injective
    simp only [LinearEquiv.apply_symm_apply,
      signedEquiv_map_rep q e₁ he₁, signedEquiv_map_rep q e₂ he₂, map_smul,
      hT.map_realStandardRep]
  · have hsrc : (⟨rightDerivative (matrixModel ℝ 3) X (f : G → ℂ),
        rightDerivative_mem_kFiniteFunctions_realStandardModule 3 ds f.2 X⟩ :
        kFiniteFunctions (realStandardModule 3 ds) (unitaryCompact ℝ 3)) =
        realStandardLie 3 ds (1 ⊗ₜ X) f := by
      apply Subtype.ext
      rw [realStandardLie_one_tmul_apply_coe]
    change e₂.symm (T (e₁ _)) =
      realStandardLie 3 es (1 ⊗ₜ X) (e₂.symm (T (e₁ f)))
    rw [hsrc]
    apply e₂.injective
    simp only [LinearEquiv.apply_symm_apply,
      signedEquiv_map_lie q e₁ he₁, signedEquiv_map_lie q e₂ he₂,
      hT.map_realStandardLie]

/-- Signed-reversal equivalences transport the existence of an injective intertwiner. -/
theorem injectiveIntertwinerExists_conjugate (q : ℕ)
    {ds es ds' es' : List RealBlock}
    (e₁ : kFiniteFunctions (realStandardModule 3 ds) (unitaryCompact ℝ 3) ≃ₗ[ℂ]
      kFiniteFunctions (realStandardModule 3 ds') (unitaryCompact ℝ 3))
    (e₂ : kFiniteFunctions (realStandardModule 3 es) (unitaryCompact ℝ 3) ≃ₗ[ℂ]
      kFiniteFunctions (realStandardModule 3 es') (unitaryCompact ℝ 3))
    (he₁ : ∀ f, (e₁ f : G → ℂ) = signedTwistLin q f)
    (he₂ : ∀ f, (e₂ f : G → ℂ) = signedTwistLin q f)
    (h : RealInjectiveIntertwinerExists 3 ds' es') :
    RealInjectiveIntertwinerExists 3 ds es := by
  obtain ⟨T, hTi, hT⟩ := h
  exact ⟨conjugateMap e₁ e₂ T, e₂.symm.injective.comp (hTi.comp e₁.injective),
    isRealStandardIntertwiner_conjugateMap q e₁ e₂ he₁ he₂ hT⟩

end Langlands.Archimedean.RealMixedSwapTwist
