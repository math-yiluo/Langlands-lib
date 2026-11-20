import Langlands.Analysis.SchwartzPartialFourier

/-! # Finite seminorm bounds for the values of a partial Fourier transform -/

noncomputable section

open Function MeasureTheory
open scoped ContDiff FourierTransform NNReal RealInnerProductSpace SchwartzMap

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

namespace Langlands.Analysis.SchwartzPartialFourier

/-- The supremum of the Schwartz seminorms of derivative order zero and weight order at most `j`. -/
def valueSeminorm {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V] (j : ℕ) :
    Seminorm ℝ 𝓢(V, ℂ) :=
  (Finset.Iic (j, 0)).sup (fun m => SchwartzMap.seminorm ℝ m.1 m.2)

theorem continuous_valueSeminorm {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V] (j : ℕ) :
    Continuous (valueSeminorm (V := V) j) :=
  Seminorm.continuous_finsetSup fun i _ => (schwartz_withSeminorms ℝ V ℂ).continuous_seminorm i

theorem valueSeminorm_smul_comp_le {V V' : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]
    [NormedAddCommGroup V'] [NormedSpace ℝ V'] (e : V' ≃L[ℝ] V) (c : ℂ) (j : ℕ) (Φ : 𝓢(V, ℂ)) :
    valueSeminorm j (c • SchwartzMap.compCLMOfContinuousLinearEquiv ℂ e Φ) ≤
      (‖c‖ * (max 1 ‖e.symm.toContinuousLinearMap‖) ^ j) * valueSeminorm j Φ := by
  let A := max 1 ‖e.symm.toContinuousLinearMap‖
  have hA : 1 ≤ A := le_max_left _ _
  have hA₀ : 0 ≤ A := zero_le_one.trans hA
  apply Seminorm.finset_sup_apply_le (by positivity)
  rintro ⟨i, n⟩ hm
  obtain ⟨hi, hn⟩ := Finset.mem_Iic.mp hm
  have hn₀ : n = 0 := Nat.eq_zero_of_le_zero hn
  subst n
  apply SchwartzMap.seminorm_le_bound ℝ i 0 _ (by positivity)
  intro x
  have hx : ‖x‖ ≤ A * ‖e x‖ := by
    calc
      ‖x‖ = ‖e.symm (e x)‖ := by rw [e.symm_apply_apply]
      _ ≤ ‖e.symm.toContinuousLinearMap‖ * ‖e x‖ :=
        e.symm.toContinuousLinearMap.le_opNorm (e x)
      _ ≤ _ := mul_le_mul_of_nonneg_right (le_max_right _ _) (norm_nonneg _)
  have hp : ‖x‖ ^ i ≤ A ^ j * ‖e x‖ ^ i := by
    calc
      _ ≤ (A * ‖e x‖) ^ i := pow_le_pow_left₀ (norm_nonneg _) hx _
      _ = A ^ i * ‖e x‖ ^ i := mul_pow _ _ _
      _ ≤ _ := mul_le_mul_of_nonneg_right (pow_le_pow_right₀ hA hi) (by positivity)
  rw [norm_iteratedFDeriv_zero]
  change ‖x‖ ^ i * ‖c • Φ (e x)‖ ≤ (‖c‖ * A ^ j) * valueSeminorm j Φ
  rw [norm_smul]
  calc
    _ ≤ (A ^ j * ‖e x‖ ^ i) * (‖c‖ * ‖Φ (e x)‖) := mul_le_mul_of_nonneg_right hp (by positivity)
    _ = (‖c‖ * A ^ j) * (‖e x‖ ^ i * ‖Φ (e x)‖) := by ring
    _ ≤ _ := mul_le_mul_of_nonneg_left ((Φ.norm_pow_mul_le_seminorm ℝ i (e x)).trans
      (Seminorm.le_finset_sup_apply (p := schwartzSeminormFamily ℝ V ℂ) (x := Φ) hm)) (by positivity)

section Slice

variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F]

private def secondSlice (x : E) : 𝓢(E × F, ℂ) →L[ℂ] 𝓢(F, ℂ) := by
  let A : F →L[ℝ] (E × F) := ContinuousLinearMap.inr ℝ E F
  have ha : (fun y : F => (x, y)) = fun y => A y + (x, 0) := by
    funext y
    simp [A]
  have ht : (fun y : F => (x, y)).HasTemperateGrowth := by
    rw [ha]
    exact A.hasTemperateGrowth.add (HasTemperateGrowth.const _)
  exact SchwartzMap.compCLM ℂ ht
    ⟨1, 1, fun y => by simpa only [pow_one, one_mul] using
      (norm_snd_le (x, y)).trans (le_add_of_nonneg_left zero_le_one)⟩

private theorem secondSlice_apply (Φ : 𝓢(E × F, ℂ)) (x : E) (y : F) :
    secondSlice x Φ y = Φ (x, y) := rfl

private theorem seminorm_secondSlice_le (Φ : 𝓢(E × F, ℂ)) (x : E) (k n : ℕ) :
    SchwartzMap.seminorm ℝ k n (secondSlice x Φ) ≤ SchwartzMap.seminorm ℝ k n Φ := by
  apply SchwartzMap.seminorm_le_bound ℝ k n _ (apply_nonneg _ _)
  intro y
  let A : F →L[ℝ] (E × F) := ContinuousLinearMap.inr ℝ E F
  let f : E × F → ℂ := fun z => Φ (z + (x, 0))
  have hfun : (secondSlice x Φ : F → ℂ) = f ∘ A := by
    funext z
    simp [secondSlice_apply, f, A]
  have hf : ContDiff ℝ ∞ f := (Φ.smooth ⊤).comp (contDiff_id.add contDiff_const)
  rw [hfun, A.iteratedFDeriv_comp_right hf y (by simp)]
  have hv : iteratedFDeriv ℝ n f (A y) = iteratedFDeriv ℝ n Φ (x, y) := by
    change iteratedFDeriv ℝ n (fun z => Φ (z + (x, 0))) (A y) = _
    rw [iteratedFDeriv_comp_add_right]
    simp [A]
  rw [hv]
  have hb := ContinuousMultilinearMap.norm_compContinuousLinearMap_le
    (iteratedFDeriv ℝ n Φ (x, y)) (fun _ => A)
  simp only [Finset.prod_const, Finset.card_univ, Fintype.card_fin] at hb
  have hA : ‖A‖ ≤ 1 := ContinuousLinearMap.norm_inr_le_one ℝ E F
  have hderiv := hb.trans ((mul_le_mul_of_nonneg_left
    (pow_le_one₀ (norm_nonneg A) hA) (norm_nonneg _)).trans_eq (mul_one _))
  calc
    _ ≤ ‖(x, y)‖ ^ k * ‖iteratedFDeriv ℝ n Φ (x, y)‖ :=
      mul_le_mul (pow_le_pow_left₀ (norm_nonneg _) (norm_snd_le (x, y)) _) hderiv (norm_nonneg _) (by positivity)
    _ ≤ _ := Φ.le_seminorm ℝ k n (x, y)

end Slice

variable {E F : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [NormedAddCommGroup F] [InnerProductSpace ℝ F]
  [FiniteDimensional ℝ E] [FiniteDimensional ℝ F]
  [MeasurableSpace E] [BorelSpace E] [MeasurableSpace F] [BorelSpace F]

private theorem transform_eq_fourier_slice (Φ : 𝓢(E × F, ℂ)) (x : E) (ξ : F) :
    transform Φ (x, ξ) = (𝓕 (secondSlice x Φ)) ξ := by
  rw [transform_apply, SchwartzMap.fourier_coe]
  rfl

/-- Complex linearity of the same partial Fourier transform of Schwartz functions. -/
def transformLinear : 𝓢(E × F, ℂ) →ₗ[ℂ] 𝓢(E × F, ℂ) where
  toFun := transform
  map_add' Φ Ψ := by
    ext ⟨x, ξ⟩
    change transform (Φ + Ψ) (x, ξ) = transform Φ (x, ξ) + transform Ψ (x, ξ)
    simp_rw [transform_eq_fourier_slice]
    let T := SchwartzMap.fourierTransformCLM ℂ (V := F) (E := ℂ)
    change T (secondSlice x (Φ + Ψ)) ξ = T (secondSlice x Φ) ξ + T (secondSlice x Ψ) ξ
    rw [map_add, map_add, add_apply]
  map_smul' c Φ := by
    ext ⟨x, ξ⟩
    change transform (c • Φ) (x, ξ) = c • transform Φ (x, ξ)
    simp_rw [transform_eq_fourier_slice]
    let T := SchwartzMap.fourierTransformCLM ℂ (V := F) (E := ℂ)
    change T (secondSlice x (c • Φ)) ξ = c • T (secondSlice x Φ) ξ
    rw [map_smul, map_smul, smul_apply]

@[simp]
theorem transformLinear_apply (Φ : 𝓢(E × F, ℂ)) : transformLinear Φ = transform Φ := rfl

private def integrableTail (y : F) : ℝ := ((1 + ‖y‖) ^ (Module.finrank ℝ F + 1))⁻¹

private theorem integrable_integrableTail : Integrable (integrableTail : F → ℝ) := by
  let q := Module.finrank ℝ F + 1
  have hq : (Module.finrank ℝ F : ℝ) < q := by
    exact_mod_cast Nat.lt_succ_self (Module.finrank ℝ F)
  refine (integrable_one_add_norm hq).congr (ae_of_all _ fun y => ?_)
  simp only [integrableTail, q, Real.rpow_neg (show 0 ≤ 1 + ‖y‖ by positivity), Real.rpow_natCast]

private theorem bound_spatial_values (j : ℕ) :
    ∃ q : Seminorm ℝ 𝓢(E × F, ℂ), Continuous q ∧
      ∀ (Φ : 𝓢(E × F, ℂ)) (x : E) (ξ : F) (i : ℕ), i ≤ j →
        ‖x‖ ^ i * ‖transform Φ (x, ξ)‖ ≤ q Φ := by
  let k := j + (Module.finrank ℝ F + 1)
  let B : ℝ := ∫ y : F, integrableTail y
  have hB : 0 ≤ B := integral_nonneg fun y => by unfold integrableTail; positivity
  let C : ℝ≥0 := ⟨2 ^ k * B, by positivity⟩
  refine ⟨C • valueSeminorm k, ?_, fun Φ x ξ i hi => ?_⟩
  · change Continuous (fun Φ : 𝓢(E × F, ℂ) => (C : ℝ) * valueSeminorm k Φ)
    exact (continuous_valueSeminorm (V := E × F) k).const_mul (C : ℝ)
  have hnorm : ‖transform Φ (x, ξ)‖ ≤ ∫ y : F, ‖Φ (x, y)‖ := by
    rw [transform_apply, Real.fourier_eq]
    exact (norm_integral_le_integral_norm _).trans_eq (by simp only [Circle.norm_smul])
  have hpoint (y : F) : ‖x‖ ^ i * ‖Φ (x, y)‖ ≤ (2 ^ k * valueSeminorm k Φ) * integrableTail y := by
    rw [integrableTail, ← div_eq_mul_inv]
    apply (le_div_iff₀ (by positivity)).2
    calc
      _ = (‖x‖ ^ i * (1 + ‖y‖) ^ (Module.finrank ℝ F + 1)) * ‖Φ (x, y)‖ := by ring
      _ ≤ (1 + ‖(x, y)‖) ^ (i + (Module.finrank ℝ F + 1)) * ‖Φ (x, y)‖ := by
        rw [pow_add (1 + ‖(x, y)‖) i (Module.finrank ℝ F + 1)]
        have hx : ‖x‖ ≤ 1 + ‖(x, y)‖ := (norm_fst_le (x, y)).trans (le_add_of_nonneg_left zero_le_one)
        have hy : 1 + ‖y‖ ≤ 1 + ‖(x, y)‖ := add_le_add le_rfl (norm_snd_le (x, y))
        gcongr
      _ ≤ _ := by
        have h := SchwartzMap.one_add_le_sup_seminorm_apply (𝕜 := ℝ) (m := (k, 0))
          (k := i + (Module.finrank ℝ F + 1)) (Nat.add_le_add_right hi _) le_rfl Φ (x, y)
        rwa [norm_iteratedFDeriv_zero] at h
  calc
    _ ≤ ‖x‖ ^ i * (∫ y : F, ‖Φ (x, y)‖) := mul_le_mul_of_nonneg_left hnorm (by positivity)
    _ = ∫ y : F, ‖x‖ ^ i * ‖Φ (x, y)‖ := (integral_const_mul _ _).symm
    _ ≤ ∫ y : F, (2 ^ k * valueSeminorm k Φ) * integrableTail y :=
      integral_mono_of_nonneg (ae_of_all _ fun _ => by positivity)
        (integrable_integrableTail.const_mul _) (ae_of_all _ hpoint)
    _ = _ := by
      rw [integral_const_mul, smul_apply, NNReal.smul_def]
      change 2 ^ k * valueSeminorm k Φ * B = (2 ^ k * B) * valueSeminorm k Φ
      ring

private theorem bound_frequency_values (j : ℕ) :
    ∃ q : Seminorm ℝ 𝓢(E × F, ℂ), Continuous q ∧
      ∀ (Φ : 𝓢(E × F, ℂ)) (x : E) (ξ : F) (i : ℕ), i ≤ j →
        ‖ξ‖ ^ i * ‖transform Φ (x, ξ)‖ ≤ q Φ := by
  let T := SchwartzMap.fourierTransformCLM ℝ (E := ℂ) (V := F)
  let p := (valueSeminorm j).comp T.toLinearMap
  have hp : Continuous p := (continuous_valueSeminorm j).comp T.continuous
  obtain ⟨s, C, _, hC⟩ := Seminorm.bound_of_continuous (schwartz_withSeminorms ℝ F ℂ) p hp
  let Q := s.sup (schwartzSeminormFamily ℝ (E × F) ℂ)
  refine ⟨C • Q, ?_, fun Φ x ξ i hi => ?_⟩
  · have hQ : Continuous Q := Seminorm.continuous_finsetSup fun m _ =>
      (schwartz_withSeminorms ℝ (E × F) ℂ).continuous_seminorm m
    change Continuous (fun Φ : 𝓢(E × F, ℂ) => (C : ℝ) * Q Φ)
    exact hQ.const_mul (C : ℝ)
  let f := secondSlice x Φ
  have he : (T f) ξ = transform Φ (x, ξ) := (transform_eq_fourier_slice Φ x ξ).symm
  rw [← he]
  have hm : (i, 0) ∈ Finset.Iic (j, 0) := Finset.mem_Iic.mpr ⟨hi, le_rfl⟩
  have hbound : (s.sup (schwartzSeminormFamily ℝ F ℂ)) f ≤ Q Φ := by
    apply Seminorm.finset_sup_apply_le (apply_nonneg _ _)
    intro m hm
    exact (seminorm_secondSlice_le Φ x m.1 m.2).trans
      (Seminorm.le_finset_sup_apply (p := schwartzSeminormFamily ℝ (E × F) ℂ) (x := Φ) hm)
  calc
    _ ≤ SchwartzMap.seminorm ℝ i 0 (T f) := (T f).norm_pow_mul_le_seminorm ℝ i ξ
    _ ≤ p f := Seminorm.le_finset_sup_apply (p := schwartzSeminormFamily ℝ F ℂ) (x := T f) hm
    _ ≤ _ := (hC f).trans (mul_le_mul_of_nonneg_left hbound C.coe_nonneg)

/-- Weighted values of the partial Fourier transform are bounded by a continuous input
seminorm, with the same bound for all weights up to `j`. -/
def SchwartzPartialFourierBoundStatement : Prop :=
  ∀ j : ℕ, ∃ q : Seminorm ℝ 𝓢(E × F, ℂ), Continuous q ∧
    ∀ Φ : 𝓢(E × F, ℂ), valueSeminorm j (transform Φ) ≤ q Φ

theorem schwartzPartialFourierBound : SchwartzPartialFourierBoundStatement (E := E) (F := F) := by
  intro j
  obtain ⟨p, hp, hspatial⟩ := bound_spatial_values (E := E) (F := F) j
  obtain ⟨q, hq, hfrequency⟩ := bound_frequency_values (E := E) (F := F) j
  refine ⟨p + q, hp.add hq, fun Φ => ?_⟩
  apply Seminorm.finset_sup_apply_le (apply_nonneg _ _)
  rintro ⟨i, n⟩ hm
  obtain ⟨hi, hn⟩ := Finset.mem_Iic.mp hm
  have hn₀ : n = 0 := Nat.eq_zero_of_le_zero hn
  subst n
  apply SchwartzMap.seminorm_le_bound ℝ i 0 _ (apply_nonneg _ _)
  rintro ⟨x, ξ⟩
  rw [norm_iteratedFDeriv_zero, Prod.norm_def]
  change max ‖x‖ ‖ξ‖ ^ i * ‖transform Φ (x, ξ)‖ ≤ p Φ + q Φ
  rcases le_total ‖x‖ ‖ξ‖ with h | h
  · rw [max_eq_right h]
    exact (hfrequency Φ x ξ i hi).trans (le_add_of_nonneg_left (apply_nonneg p Φ))
  · rw [max_eq_left h]
    exact (hspatial Φ x ξ i hi).trans (le_add_of_nonneg_right (apply_nonneg q Φ))

/-- The weighted value bound is preserved under continuous linear preprocessing, a fixed
linear coordinate change on the output, and constant rescaling of the output. -/
theorem exists_bound_transform_pullback {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]
    (L : 𝓢(V, ℂ) →L[ℂ] 𝓢(E × F, ℂ)) (e : V ≃L[ℝ] (E × F)) (c : ℂ) (j : ℕ) :
    ∃ q : Seminorm ℝ 𝓢(V, ℂ), Continuous q ∧
      ∀ Φ : 𝓢(V, ℂ), valueSeminorm j (c • SchwartzMap.compCLMOfContinuousLinearEquiv ℂ e
        (transform (L Φ))) ≤ q Φ := by
  obtain ⟨q, hq, hb⟩ := schwartzPartialFourierBound (E := E) (F := F) j
  let C : ℝ≥0 := ⟨‖c‖ * (max 1 ‖e.symm.toContinuousLinearMap‖) ^ j, by positivity⟩
  refine ⟨C • q.comp (L.restrictScalars ℝ).toLinearMap, ?_, fun Φ => ?_⟩
  · change Continuous (fun Φ : 𝓢(V, ℂ) => (C : ℝ) * q (L Φ))
    exact (hq.comp L.continuous).const_mul _
  change _ ≤ (C : ℝ) * q (L Φ)
  exact (valueSeminorm_smul_comp_le e c j (transform (L Φ))).trans
    (mul_le_mul_of_nonneg_left (hb (L Φ)) C.coe_nonneg)

end Langlands.Analysis.SchwartzPartialFourier
