import Langlands.Global.RankinSelberg.EqualAnalyticProduct
import Langlands.Automorphic.CuspidalWhittaker.AdelicCharacter
import Mathlib.Analysis.Fourier.FourierTransformDeriv
import Mathlib.Analysis.Distribution.SchwartzSpace.Basic

/-! # Rapid decay of archimedean Fourier transforms for the trace pairing

For a Schwartz function `f` on a finite-dimensional real space and a continuous bilinear form
`L` which is nondegenerate in its second variable, the Fourier transform
`w ↦ ∫ e(-L v w) f(v) dv` decays faster than every power of `‖w‖`. This is applied to the
pairing `(v, w) ↦ Tr_∞(β Σ_j v_j w_j)` on `(F_∞)^n` for a unit `β` of the mixed space.
-/

noncomputable section
universe u
open NumberField MeasureTheory Set
open scoped Classical FourierTransform
set_option autoImplicit false

namespace Langlands.Global.RankinSelbergGlobal.EqualAnalytic

open Langlands.Global Langlands.Automorphic.CuspidalWhittaker

section Generic

variable {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V] [FiniteDimensional ℝ V]
  [MeasurableSpace V] [BorelSpace V] (mu : Measure V) [mu.IsAddHaarMeasure]

omit [MeasurableSpace V] [BorelSpace V] in
/-- A nondegenerate family of linear functionals controls the norm. -/
theorem exists_norm_le_sum_of_injective {ι : Type*} [Fintype ι] (Λ : V →ₗ[ℝ] (ι → ℝ))
    (hΛ : Function.Injective Λ) : ∃ K : ℝ, 0 ≤ K ∧ ∀ w, ‖w‖ ≤ K * ∑ i, |Λ w i| := by
  let e : V ≃ₗ[ℝ] LinearMap.range Λ := LinearEquiv.ofInjective Λ hΛ
  let es : LinearMap.range Λ →L[ℝ] V := LinearMap.toContinuousLinearMap e.symm.toLinearMap
  refine ⟨‖es‖, es.opNorm_nonneg, fun w => ?_⟩
  have h1 : w = es (e w) := by simp [es]
  have h2 : ‖(e w : LinearMap.range Λ)‖ = ‖Λ w‖ := rfl
  have h3 : ‖Λ w‖ ≤ ∑ i, |Λ w i| := by
    refine (pi_norm_le_iff_of_nonneg (Finset.sum_nonneg fun i _ => abs_nonneg _)).mpr
      fun i => ?_
    rw [Real.norm_eq_abs]
    exact Finset.single_le_sum (f := fun i => |Λ w i|) (fun i _ => abs_nonneg _)
      (Finset.mem_univ i)
  calc ‖w‖ = ‖es (e w)‖ := by rw [← h1]
    _ ≤ ‖es‖ * ‖(e w : LinearMap.range Λ)‖ := es.le_opNorm _
    _ ≤ ‖es‖ * ∑ i, |Λ w i| := by
      rw [h2]
      exact mul_le_mul_of_nonneg_left h3 es.opNorm_nonneg

theorem one_add_pow_le (x : ℝ) (hx : 0 ≤ x) (N : ℕ) :
    (1 + x) ^ N ≤ 2 ^ N * (1 + x ^ N) := by
  rcases le_total x 1 with h | h
  · calc (1 + x) ^ N ≤ 2 ^ N := pow_le_pow_left₀ (by positivity) (by linarith) N
      _ ≤ 2 ^ N * (1 + x ^ N) := by
        have : 0 ≤ x ^ N := pow_nonneg hx N
        nlinarith [pow_pos (show (0 : ℝ) < 2 by norm_num) N]
  · calc (1 + x) ^ N ≤ (2 * x) ^ N := pow_le_pow_left₀ (by positivity) (by linarith) N
      _ = 2 ^ N * x ^ N := mul_pow 2 x N
      _ ≤ 2 ^ N * (1 + x ^ N) := by
        have : 0 ≤ (2 : ℝ) ^ N := by positivity
        nlinarith

/-- **Rapid decay.** If the functionals `L (v i)` jointly separate points, the Fourier transform
of a Schwartz function decays faster than every power. -/
theorem exists_fourierIntegral_decay (L : V →L[ℝ] V →L[ℝ] ℝ) {ι : Type*} [Fintype ι]
    (v : ι → V) (hinj : ∀ w, (∀ i, L (v i) w = 0) → w = 0) (f : SchwartzMap V ℂ) (N : ℕ) :
    ∃ C : ℝ, ∀ w, (1 + ‖w‖) ^ N *
      ‖VectorFourier.fourierIntegral 𝐞 mu L.toLinearMap₁₂ f w‖ ≤ C := by
  set G := VectorFourier.fourierIntegral 𝐞 mu L.toLinearMap₁₂ (f : V → ℂ) with hG
  -- the bound for each separating functional
  have hbound : ∀ (i : ι) (M : ℕ), ∃ A : ℝ, ∀ w, |L (v i) w| ^ M * ‖G w‖ ≤ A := by
    intro i M
    refine ⟨‖v i‖ ^ M * (2 * Real.pi * ‖L‖) ^ 0 * (2 * (0 : ℕ) + 2) ^ M *
      ∑ p ∈ Finset.range (0 + 1) ×ˢ Finset.range (M + 1),
        ∫ x, ‖x‖ ^ p.1 * ‖iteratedFDeriv ℝ p.2 (f : V → ℂ) x‖ ∂mu, fun w => ?_⟩
    have h := VectorFourier.pow_mul_norm_iteratedFDeriv_fourierIntegral_le (L := L) (μ := mu)
      (f := (f : V → ℂ)) (K := 0) (N := ⊤) (f.smooth ⊤)
      (fun k m _ _ => f.integrable_pow_mul_iteratedFDeriv mu k m) (k := 0) (n := M)
      le_rfl (by exact_mod_cast le_top) (v i) w
    rw [norm_iteratedFDeriv_zero] at h
    exact h
  rcases isEmpty_or_nonempty ι with hι | hι
  · refine ⟨‖G 0‖, fun w => ?_⟩
    have : w = 0 := hinj w fun i => (hι.false i).elim
    subst this
    simp
  obtain ⟨i₁⟩ := hι
  have hbound0 : ∃ A : ℝ, ∀ w, ‖G w‖ ≤ A := by
    obtain ⟨A, hA⟩ := hbound i₁ 0
    exact ⟨A, fun w => by simpa using hA w⟩
  choose A hA using hbound
  obtain ⟨A₀, hA₀⟩ := hbound0
  let Λ : V →ₗ[ℝ] (ι → ℝ) :=
    { toFun := fun w i => L (v i) w
      map_add' := fun w w' => by funext i; simp
      map_smul' := fun c w => by funext i; simp }
  have hΛ : Function.Injective Λ := by
    rw [← LinearMap.ker_eq_bot, LinearMap.ker_eq_bot']
    intro w hw
    exact hinj w fun i => congrFun hw i
  obtain ⟨K, hK, hKw⟩ := exists_norm_le_sum_of_injective Λ hΛ
  set m := Fintype.card ι
  refine ⟨2 ^ N * (A₀ + (K * m) ^ N * ∑ i, A i N), fun w => ?_⟩
  have hGn : 0 ≤ ‖G w‖ := norm_nonneg _
  -- `‖w‖^N ‖G w‖` is bounded
  have hpow : ‖w‖ ^ N * ‖G w‖ ≤ (K * m) ^ N * ∑ i, A i N := by
    obtain ⟨i₀, -, hi₀⟩ := Finset.exists_max_image Finset.univ (fun i => |L (v i) w|)
      ⟨i₁, Finset.mem_univ _⟩
    have hsum : ∑ i, |L (v i) w| ≤ m * |L (v i₀) w| := by
      calc ∑ i, |L (v i) w| ≤ ∑ _i : ι, |L (v i₀) w| :=
            Finset.sum_le_sum fun i hi => hi₀ i hi
        _ = m * |L (v i₀) w| := by simp [m]
    have hw : ‖w‖ ≤ K * m * |L (v i₀) w| := by
      calc ‖w‖ ≤ K * ∑ i, |Λ w i| := hKw w
        _ ≤ K * (m * |L (v i₀) w|) := mul_le_mul_of_nonneg_left hsum hK
        _ = K * m * |L (v i₀) w| := by ring
    have hA0 : ∀ i, 0 ≤ A i N := fun i =>
      le_trans (mul_nonneg (pow_nonneg (abs_nonneg _) _) hGn) (hA i N w)
    calc ‖w‖ ^ N * ‖G w‖ ≤ (K * m * |L (v i₀) w|) ^ N * ‖G w‖ :=
          mul_le_mul_of_nonneg_right (pow_le_pow_left₀ (norm_nonneg _) hw N) hGn
      _ = (K * m) ^ N * (|L (v i₀) w| ^ N * ‖G w‖) := by ring
      _ ≤ (K * m) ^ N * A i₀ N :=
          mul_le_mul_of_nonneg_left (hA i₀ N w) (pow_nonneg (by positivity) N)
      _ ≤ (K * m) ^ N * ∑ i, A i N :=
          mul_le_mul_of_nonneg_left
            (Finset.single_le_sum (fun i _ => hA0 i) (Finset.mem_univ i₀))
            (pow_nonneg (by positivity) N)
  calc (1 + ‖w‖) ^ N * ‖G w‖ ≤ 2 ^ N * (1 + ‖w‖ ^ N) * ‖G w‖ :=
        mul_le_mul_of_nonneg_right (one_add_pow_le _ (norm_nonneg _) N) hGn
    _ = 2 ^ N * (‖G w‖ + ‖w‖ ^ N * ‖G w‖) := by ring
    _ ≤ 2 ^ N * (A₀ + (K * m) ^ N * ∑ i, A i N) := by
        gcongr
        · exact hA₀ w

end Generic

section Trace

variable (F : Type u) [Field F] [NumberField F] (n : ℕ)

/-- The bilinear form `(v, w) ↦ Tr_∞(β Σ_j v_j w_j)` on `(F_∞)^n`. -/
def traceBilin (β : mixedEmbedding.mixedSpace F) :
    ArchRow F n →ₗ[ℝ] ArchRow F n →ₗ[ℝ] ℝ :=
  LinearMap.mk₂ ℝ (fun v w => mixedTrace F (β * ∑ j, v j * w j))
    (fun v v' w => by
      simp only [Pi.add_apply, add_mul, Finset.sum_add_distrib, mul_add, map_add])
    (fun c v w => by
      simp only [Pi.smul_apply, smul_mul_assoc, ← Finset.smul_sum, mul_smul_comm, map_smul])
    (fun v w w' => by
      simp only [Pi.add_apply, mul_add, Finset.sum_add_distrib, map_add])
    (fun c v w => by
      simp only [Pi.smul_apply, mul_smul_comm, ← Finset.smul_sum, map_smul])

/-- The trace pairing as a continuous bilinear map. -/
def tracePairing (β : mixedEmbedding.mixedSpace F) :
    ArchRow F n →L[ℝ] ArchRow F n →L[ℝ] ℝ :=
  LinearMap.toContinuousLinearMap
    ((LinearMap.toContinuousLinearMap :
      (ArchRow F n →ₗ[ℝ] ℝ) ≃ₗ[ℝ] (ArchRow F n →L[ℝ] ℝ)).toLinearMap.comp
        (traceBilin F n β))

theorem tracePairing_apply (β : mixedEmbedding.mixedSpace F) (v w : ArchRow F n) :
    tracePairing F n β v w = mixedTrace F (β * ∑ j, v j * w j) := rfl

theorem neg_tracePairing_toLinearMap₁₂_apply (β : mixedEmbedding.mixedSpace F)
    (v w : ArchRow F n) :
    (-tracePairing F n β).toLinearMap₁₂ v w = -mixedTrace F (β * ∑ j, v j * w j) := rfl

theorem mixedTracePairing_apply (Y : mixedEmbedding.mixedSpace F)
    (k : Module.Free.ChooseBasisIndex ℤ (RingOfIntegers F)) :
    mixedTracePairing F Y k = mixedTrace F (mixedEmbedding.latticeBasis F k * Y) := rfl

/-- The trace pairing is nondegenerate when `β` is a unit. -/
theorem tracePairing_separates (β β' : mixedEmbedding.mixedSpace F) (hβ : β * β' = 1)
    (w : ArchRow F n)
    (hw : ∀ p : Fin n × Module.Free.ChooseBasisIndex ℤ (RingOfIntegers F),
      tracePairing F n β (Pi.single p.1 (mixedEmbedding.latticeBasis F p.2 * β')) w = 0) :
    w = 0 := by
  funext j
  have hj : mixedTracePairing F (w j) = 0 := by
    funext k
    have h := hw (j, k)
    rw [tracePairing_apply] at h
    have hsum : ∑ l, (Pi.single j (mixedEmbedding.latticeBasis F k * β') :
        ArchRow F n) l * w l = mixedEmbedding.latticeBasis F k * β' * w j := by
      rw [Finset.sum_eq_single j]
      · simp
      · intro l _ hl
        simp [hl]
      · simp
    rw [hsum, show β * (mixedEmbedding.latticeBasis F k * β' * w j) =
      mixedEmbedding.latticeBasis F k * w j by
        rw [show β * (mixedEmbedding.latticeBasis F k * β' * w j) =
          mixedEmbedding.latticeBasis F k * (β * β') * w j by ring, hβ, mul_one]] at h
    rw [mixedTracePairing_apply]
    exact h
  have := mixedTracePairing_injective F (hj.trans (map_zero _).symm)
  rw [this]
  rfl

/-- **Rapid decay of the archimedean Fourier transform** for the trace pairing. -/
theorem exists_archimedeanFourier_decay (β β' : mixedEmbedding.mixedSpace F)
    (hβ : β * β' = 1) (f : SchwartzMap (ArchRow F n) ℂ) (N : ℕ) :
    ∃ C : ℝ, ∀ w : ArchRow F n, (1 + ‖w‖) ^ N *
      ‖∫ v, f v * (𝐞 (mixedTrace F (β * ∑ j, v j * w j)) : ℂ)‖ ≤ C := by
  obtain ⟨C, hC⟩ := exists_fourierIntegral_decay (volume : Measure (ArchRow F n))
    (-tracePairing F n β)
    (fun p : Fin n × Module.Free.ChooseBasisIndex ℤ (RingOfIntegers F) =>
      Pi.single p.1 (mixedEmbedding.latticeBasis F p.2 * β'))
    (fun w hw => tracePairing_separates F n β β' hβ w fun p => by
      have := hw p
      simpa using this) f N
  refine ⟨C, fun w => ?_⟩
  convert hC w using 3
  simp only [VectorFourier.fourierIntegral, neg_tracePairing_toLinearMap₁₂_apply, neg_neg,
    Circle.smul_def, smul_eq_mul]
  congr 1
  funext v
  exact mul_comm _ _

theorem continuous_archimedeanFourier (β : mixedEmbedding.mixedSpace F)
    (f : SchwartzMap (ArchRow F n) ℂ) :
    Continuous fun w : ArchRow F n =>
      ∫ v, f v * (𝐞 (mixedTrace F (β * ∑ j, v j * w j)) : ℂ) := by
  have h := VectorFourier.fourierIntegral_continuous (μ := (volume : Measure (ArchRow F n)))
    Real.continuous_fourierChar (L := (-tracePairing F n β).toLinearMap₁₂)
    (-tracePairing F n β).continuous₂ f.integrable
  convert h using 1
  funext w
  simp only [VectorFourier.fourierIntegral, neg_tracePairing_toLinearMap₁₂_apply, neg_neg,
    Circle.smul_def, smul_eq_mul]
  congr 1
  funext v
  exact mul_comm _ _

end Trace

end Langlands.Global.RankinSelbergGlobal.EqualAnalytic
