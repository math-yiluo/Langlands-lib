import Langlands.Representation.Archimedean.GardingFunctionals
import Mathlib.Analysis.InnerProductSpace.Dual
import Mathlib.LinearAlgebra.Isomorphisms

/-! # Smoothness of the Hilbert vectors of regularized functionals -/

noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open MeasureTheory Set
open scoped Manifold ContDiff InnerProductSpace NNReal

namespace Langlands.Archimedean

universe uA uG uE

variable {A : Type uA} [NormedAddCommGroup A] [NormedSpace ℝ A]
  {G : Type uG} [Group G] [TopologicalSpace G] [ChartedSpace A G]
  [LieGroup 𝓘(ℝ, A) ∞ G]

section WordSum

variable {E : Type uE} [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E]
  (π : G →* (E →L[ℂ] E))

/-- A smooth-vector functional with a finite derivative bound is a finite
sum of Hilbert pairings against those genuine word derivatives. -/
theorem exists_inner_word_sum (ℓ : smoothVectors 𝓘(ℝ, A) π →ₗ[ℂ] ℂ)
    (hℓ : IsContinuousOnSmoothVectors 𝓘(ℝ, A) π ℓ) :
    ∃ (S : Finset (List A)) (w : S → E), ∀ v : smoothVectors 𝓘(ℝ, A) π,
      ℓ v = ∑ i : S, inner ℂ (w i) (iteratedLieDerivative 𝓘(ℝ, A) π i.val v) := by
  classical
  obtain ⟨S, C, hC⟩ := hℓ
  let c : ℝ≥0 := ⟨max 0 C, le_max_left _ _⟩
  let D : smoothVectors 𝓘(ℝ, A) π →ₗ[ℂ] (S → E) :=
    LinearMap.pi fun i => (smoothVectors 𝓘(ℝ, A) π).subtype.comp
      (smoothIteratedLieDerivative 𝓘(ℝ, A) π i.val)
  have hD (v : smoothVectors 𝓘(ℝ, A) π) (i : S) :
      D v i = iteratedLieDerivative 𝓘(ℝ, A) π i.val v :=
    smoothIteratedLieDerivative_apply 𝓘(ℝ, A) π i.val v
  have hb (v : smoothVectors 𝓘(ℝ, A) π) : ‖ℓ v‖ ≤ (c : ℝ) * ∑ i : S, ‖D v i‖ := by
    simp_rw [hD]
    rw [Finset.sum_coe_sort S (fun Xs => ‖iteratedLieDerivative 𝓘(ℝ, A) π Xs v‖)]
    exact (hC v).trans (mul_le_mul_of_nonneg_right (le_max_right _ _)
      (Finset.sum_nonneg fun _ _ => norm_nonneg _))
  have hker : D.ker ≤ ℓ.ker := by
    intro v hv
    rw [LinearMap.mem_ker] at hv ⊢
    apply norm_le_zero_iff.mp
    simpa only [hv, Pi.zero_apply, norm_zero, Finset.sum_const_zero, mul_zero] using hb v
  let L : D.range →ₗ[ℂ] ℂ :=
    (D.ker.liftQ ℓ hker).comp D.quotKerEquivRange.symm.toLinearMap
  have hL (v : smoothVectors 𝓘(ℝ, A) π) : L (D.rangeRestrict v) = ℓ v := by
    change D.ker.liftQ ℓ hker (D.quotKerEquivRange.symm ⟨D v, _⟩) = ℓ v
    rw [LinearMap.quotKerEquivRange_symm_apply_image, Submodule.mkQ_apply, Submodule.liftQ_apply]
  let p : Seminorm ℂ (S → E) := c • ∑ i : S, (normSeminorm ℂ E).comp (LinearMap.proj i)
  have hp (z : S → E) : p z = (c : ℝ) * ∑ i : S, ‖z i‖ := by
    simp only [p, smul_apply, NNReal.smul_def, smul_eq_mul, FunLike.coe_sum, Finset.sum_apply,
      Seminorm.comp_apply, LinearMap.proj_apply]
    rfl
  obtain ⟨T, hT, hTp⟩ := Module.Dual.exists_extension_of_le_seminorm D.range L (p := p) (by
    intro z
    obtain ⟨v, rfl⟩ := D.surjective_rangeRestrict z
    rw [hL, hp]
    exact hb v)
  let Ti (i : S) : E →L[ℂ] ℂ := (T.comp (LinearMap.single ℂ (fun _ : S => E) i)).mkContinuous c (by
    intro v
    change ‖T (Pi.single i v)‖ ≤ _
    refine (hTp _).trans_eq ?_
    rw [hp]
    congr 1
    calc
      _ = ∑ j : S, if j = i then ‖v‖ else 0 := by
        apply Finset.sum_congr rfl
        intro j _
        by_cases h : j = i
        · subst j
          simp
        · simp [h]
      _ = _ := by simp)
  let w (i : S) : E := (InnerProductSpace.toDual ℂ E).symm (Ti i)
  have hw (i : S) (v : E) : inner ℂ (w i) v = T (Pi.single i v) := by
    have h := DFunLike.congr_fun ((InnerProductSpace.toDual ℂ E).apply_symm_apply (Ti i)) v
    exact h
  refine ⟨S, w, fun v => ?_⟩
  simp_rw [← hD, hw, ← map_sum, LinearMap.sum_single_apply]
  exact (hL v).symm.trans (hT (D.rangeRestrict v)).symm

end WordSum

/-- Conjugate reversal of a compact smooth kernel. -/
def adjointGardingKernel (φ : smoothCompactKernels A G) : smoothCompactKernels A G := by
  let : ContinuousInv G := ⟨(contMDiff_id.inv :
    ContMDiff 𝓘(ℝ, A) 𝓘(ℝ, A) ∞ (Inv.inv : G → G)).continuous⟩
  refine ⟨fun x => star (φ.val x⁻¹), ⟨?_, ?_⟩⟩
  · exact (RCLike.conjCLE : ℂ ≃L[ℝ] ℂ).contDiff.contMDiff.comp
      (φ.property.1.comp contMDiff_id.inv)
  · have hc : HasCompactSupport (φ.val ∘ (Inv.inv : G → G)) :=
      φ.property.2.comp_isClosedEmbedding (Homeomorph.inv G).isClosedEmbedding
    exact hc.comp_left (g := star) (star_zero ℂ)

variable [FiniteDimensional ℝ A] [T2Space G] [LocallyCompactSpace G]
  [MeasurableSpace G] [BorelSpace G] (μ : Measure G) [μ.IsHaarMeasure] [μ.IsInvInvariant]
  {E : Type uE} [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E]
  (π : G →* (E →L[ℂ] E)) (hπ : IsContinuousRepresentation π)

include hπ in
/-- Moving a compact average across the unitary pairing conjugates and
inverts its kernel. -/
theorem inner_adjointGardingIntegral (hπu : ∀ g v w, inner ℂ (π g v) (π g w) = inner ℂ v w)
    (φ : smoothCompactKernels A G) (w v : E) :
    inner ℂ (gardingIntegralLinearMap μ π hπ (adjointGardingKernel φ) w : E) v =
      inner ℂ w (gardingIntegralLinearMap μ π hπ φ v : E) := by
  let : ContinuousInv G := ⟨(contMDiff_id.inv :
    ContMDiff 𝓘(ℝ, A) 𝓘(ℝ, A) ∞ (Inv.inv : G → G)).continuous⟩
  let L : E →L[ℝ] ℂ := (RCLike.conjCLE : ℂ ≃L[ℝ] ℂ).toContinuousLinearMap.comp
    ((innerSL ℂ v).restrictScalars ℝ)
  have hL (z : E) : L z = inner ℂ z v := inner_conj_symm z v
  have hu (g : G) : inner ℂ (π g w) v = inner ℂ w (π g⁻¹ v) := by
    have hg : π g⁻¹ (π g w) = w := by
      change (π g⁻¹ * π g) w = w
      simp [← map_mul]
    rw [← hπu g⁻¹ (π g w) v, hg]
  calc
    _ = ∫ x, inner ℂ ((adjointGardingKernel φ).val x • π x w) v ∂μ := by
      simp only [← hL]
      exact (L.integral_comp_comm
        (integrable_gardingIntegrand μ π hπ (adjointGardingKernel φ) w)).symm
    _ = ∫ x, φ.val x⁻¹ * inner ℂ w (π x⁻¹ v) ∂μ := by
      apply integral_congr_ae (Filter.Eventually.of_forall fun x => ?_)
      rw [inner_smul_left, hu]
      change star (star (φ.val x⁻¹)) * _ = _
      rw [star_star]
    _ = ∫ x, φ.val x * inner ℂ w (π x v) ∂μ :=
      integral_inv_eq_self (fun x => φ.val x * inner ℂ w (π x v)) μ
    _ = _ := by
      change _ = inner ℂ w (∫ x, φ.val x • π x v ∂μ)
      simpa only [map_smul, smul_eq_mul, innerSL_apply_apply] using
        (innerSL ℂ w).integral_comp_comm (integrable_gardingIntegrand μ π hπ φ v)

include hπ in
/-- For each kernel, the Riesz vector of the bounded regularization of a
derivative-continuous smooth functional is a genuine smooth vector. -/
theorem isSmoothVector_gardingRiesz (hπu : ∀ g v w, inner ℂ (π g v) (π g w) = inner ℂ v w)
    (hunitary : ∀ g v, ‖π g v‖ = ‖v‖)
    (ℓ : smoothVectors 𝓘(ℝ, A) π →ₗ[ℂ] ℂ) (hℓ : IsContinuousOnSmoothVectors 𝓘(ℝ, A) π ℓ)
    (φ : smoothCompactKernels A G) :
    IsSmoothVector 𝓘(ℝ, A) π
      ((InnerProductSpace.toDual ℂ E).symm (gardingFunctional μ π hπ hunitary ℓ hℓ φ)) := by
  classical
  obtain ⟨S, w, hw⟩ := exists_inner_word_sum π ℓ hℓ
  let ψ (i : S) : smoothCompactKernels A G :=
    ⟨gardingKernelWord i.val φ.val,
      gardingKernelWord_smooth_compact i.val φ.property.1 φ.property.2⟩
  let z (i : S) : smoothVectors 𝓘(ℝ, A) π :=
    gardingIntegralLinearMap μ π hπ (adjointGardingKernel (ψ i)) (w i)
  have hsum : ((∑ i : S, z i : smoothVectors 𝓘(ℝ, A) π) : E) =
      (InnerProductSpace.toDual ℂ E).symm (gardingFunctional μ π hπ hunitary ℓ hℓ φ) := by
    apply (InnerProductSpace.toDual ℂ E).injective
    rw [LinearIsometryEquiv.apply_symm_apply]
    apply ContinuousLinearMap.ext
    intro v
    rw [InnerProductSpace.toDual_apply_apply, gardingFunctional_apply, hw]
    change inner ℂ ((smoothVectors 𝓘(ℝ, A) π).subtype (∑ i : S, z i)) v = _
    rw [map_sum, sum_inner]
    apply Finset.sum_congr rfl
    intro i _
    calc
      _ = inner ℂ (w i) (gardingIntegralLinearMap μ π hπ (ψ i) v : E) :=
        inner_adjointGardingIntegral μ π hπ hπu (ψ i) (w i) v
      _ = _ := congrArg (inner ℂ (w i))
        (iteratedLieDerivative_gardingIntegral μ π hπ φ.val φ.property.1
          φ.property.2 v i.val).symm
  rw [← hsum]
  exact (∑ i : S, z i : smoothVectors 𝓘(ℝ, A) π).property

end Langlands.Archimedean
