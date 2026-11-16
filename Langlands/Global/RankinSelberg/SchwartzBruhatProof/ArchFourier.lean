import Mathlib.Analysis.Distribution.SchwartzSpace.Fourier
import Mathlib.Analysis.Fourier.Inversion
import Mathlib.Analysis.InnerProductSpace.EuclideanDist
import Mathlib.MeasureTheory.Measure.Haar.Unique

/-! # Fourier analysis for a symmetric nondegenerate pairing on a real vector space

For a finite-dimensional real vector space `W` with an additive Haar measure `μ` and a
symmetric bilinear form `B` with trivial kernel, the Fourier transform
`F_B φ(ξ) = ∫ φ(w) 𝐞(B(w, ξ)) dμ(w)` is transported to Mathlib's Fourier transform on a
Euclidean space through linear isomorphisms `P, Q` with `B(w, ξ) = ⟪P w, Q ξ⟫`. It maps
Schwartz functions to Schwartz functions and there is one constant `C` with
`F_B F_B φ = C · φ(-·)` for every Schwartz function `φ`.
-/

noncomputable section
open MeasureTheory Module
open scoped FourierTransform RealInnerProductSpace NNReal ENNReal Real
set_option autoImplicit false

namespace Langlands.Global.RankinSelbergGlobal.SchwartzBruhatProof

section Generic

variable {W : Type*} [NormedAddCommGroup W] [NormedSpace ℝ W] [FiniteDimensional ℝ W]
  [MeasurableSpace W] [BorelSpace W]
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  [MeasurableSpace E] [BorelSpace E]

/-- The Fourier transform `F_B φ(ξ) = ∫ φ(w) 𝐞(B(w, ξ)) dμ(w)` for a bilinear form `B`. -/
def pairingFourier (μ : Measure W) (B : W →ₗ[ℝ] W →ₗ[ℝ] ℝ) (φ : W → ℂ) (ξ : W) : ℂ :=
  ∫ w, φ w * (𝐞 (B w ξ) : ℂ) ∂μ

omit [FiniteDimensional ℝ W] in
/-- The image of a Haar measure under a linear isomorphism onto a Euclidean space is a
positive multiple of the volume. -/
theorem exists_map_eq_smul_volume (μ : Measure W) [μ.IsAddHaarMeasure] (P : W ≃L[ℝ] E) :
    ∃ c : ℝ≥0, c ≠ 0 ∧ μ.map P = (c : ℝ≥0∞) • volume := by
  have h := Measure.isAddLeftInvariant_eq_smul (μ.map P) (volume : Measure E)
  refine ⟨Measure.addHaarScalarFactor (μ.map P) volume, fun h0 => ?_, by
    rw [← ENNReal.smul_def]; exact h⟩
  rw [h0, zero_smul] at h
  have hpos : (μ.map P) Set.univ ≠ 0 := (isOpen_univ.measure_pos _ Set.univ_nonempty).ne'
  exact hpos (by rw [h]; rfl)

omit [MeasurableSpace W] [BorelSpace W] [MeasurableSpace E] [BorelSpace E] in
/-- For a pairing with trivial right kernel and a linear isomorphism `P`, there is a linear
isomorphism `Q` with `B(w, ξ) = ⟪P w, Q ξ⟫`. -/
theorem exists_inner_eq (B : W →ₗ[ℝ] W →ₗ[ℝ] ℝ) (hB : ∀ ξ, (∀ w, B w ξ = 0) → ξ = 0)
    (P : W ≃L[ℝ] E) : ∃ Q : W ≃L[ℝ] E, ∀ w ξ, B w ξ = ⟪P w, Q ξ⟫ := by
  classical
  let b := stdOrthonormalBasis ℝ E
  let Q₀ : W →ₗ[ℝ] E := ∑ i, (B (P.symm (b i))).smulRight (b i)
  have hQ₀ : ∀ ξ, Q₀ ξ = ∑ i, B (P.symm (b i)) ξ • b i := fun ξ => by
    simp [Q₀, LinearMap.sum_apply]
  have key : ∀ w ξ, B w ξ = ⟪P w, Q₀ ξ⟫ := by
    intro w ξ
    rw [hQ₀, inner_sum]
    conv_lhs => rw [← P.symm_apply_apply w, ← b.sum_repr' (P w)]
    simp only [map_sum, map_smul, LinearMap.sum_apply, LinearMap.smul_apply, smul_eq_mul,
      real_inner_smul_right]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [real_inner_comm]
    ring
  have hinj : Function.Injective Q₀ := by
    rw [← LinearMap.ker_eq_bot, LinearMap.ker_eq_bot']
    intro ξ hξ
    exact hB ξ fun w => by rw [key, hξ, inner_zero_right]
  have hsurj : Function.Surjective Q₀ :=
    (LinearMap.injective_iff_surjective_of_finrank_eq_finrank
      P.toLinearEquiv.finrank_eq).mp hinj
  let Qe : W ≃ₗ[ℝ] E := LinearEquiv.ofBijective Q₀ ⟨hinj, hsurj⟩
  exact ⟨Qe.toContinuousLinearEquiv, fun w ξ => key w ξ⟩

omit [FiniteDimensional ℝ W] in
/-- Transport of `F_B` to Mathlib's inverse Fourier transform. -/
theorem pairingFourier_eq (μ : Measure W) (B : W →ₗ[ℝ] W →ₗ[ℝ] ℝ) (P Q : W ≃L[ℝ] E)
    (hPQ : ∀ w ξ, B w ξ = ⟪P w, Q ξ⟫) {c : ℝ≥0} (hc : μ.map P = (c : ℝ≥0∞) • volume)
    (φ : W → ℂ) (ξ : W) :
    pairingFourier μ B φ ξ = ((c : ℝ) : ℂ) * 𝓕⁻ (φ ∘ P.symm) (Q ξ) := by
  have h := integral_map_equiv (μ := μ) P.toHomeomorph.toMeasurableEquiv
    (fun y : E => φ (P.symm y) * (𝐞 ⟪y, Q ξ⟫ : ℂ))
  simp only [Homeomorph.toMeasurableEquiv_coe, ContinuousLinearEquiv.coe_toHomeomorph,
    ContinuousLinearEquiv.symm_apply_apply] at h
  unfold pairingFourier
  simp_rw [hPQ]
  rw [← h, hc, integral_smul_measure, Real.fourierInv_eq]
  simp only [ENNReal.coe_toReal, Circle.smul_def, smul_eq_mul, Function.comp_apply,
    Complex.real_smul]
  congr 1
  refine integral_congr_ae (Filter.Eventually.of_forall fun y => ?_)
  exact mul_comm _ _

omit [FiniteDimensional ℝ W] in
theorem integrable_of_comp {μ : Measure W} {f : E → ℂ} {e : W ≃L[ℝ] E} {c : ℝ≥0}
    (hc : μ.map e = (c : ℝ≥0∞) • volume) (hc0 : c ≠ 0) (hf : Integrable (f ∘ e) μ) :
    Integrable f volume := by
  have h1 : Integrable f (μ.map e) :=
    (integrable_map_equiv e.toHomeomorph.toMeasurableEquiv f).mpr hf
  rw [hc] at h1
  exact (integrable_smul_measure (ENNReal.coe_ne_zero.mpr hc0) ENNReal.coe_ne_top).mp h1

omit [FiniteDimensional ℝ W] in
/-- **Fourier inversion** for `F_B`: `F_B F_B φ = c_P c_Q φ(-·)` for continuous integrable `φ`
with integrable `F_B φ`. -/
theorem pairingFourier_pairingFourier (μ : Measure W) (B : W →ₗ[ℝ] W →ₗ[ℝ] ℝ)
    (hsymm : ∀ w ξ, B w ξ = B ξ w) (P Q : W ≃L[ℝ] E) (hPQ : ∀ w ξ, B w ξ = ⟪P w, Q ξ⟫)
    {cP cQ : ℝ≥0} (hcP : μ.map P = (cP : ℝ≥0∞) • volume)
    (hcQ : μ.map Q = (cQ : ℝ≥0∞) • volume) (hcP0 : cP ≠ 0) (hcQ0 : cQ ≠ 0)
    {φ : W → ℂ} (hφc : Continuous φ) (hφi : Integrable φ μ)
    (hFi : Integrable (pairingFourier μ B φ) μ) (x : W) :
    pairingFourier μ B (pairingFourier μ B φ) x =
      ((cP : ℝ) : ℂ) * ((cQ : ℝ) : ℂ) * φ (-x) := by
  have hQP : ∀ w ξ, B w ξ = ⟪Q w, P ξ⟫ := fun w ξ => by rw [hsymm, hPQ, real_inner_comm]
  set g : E → ℂ := φ ∘ Q.symm with hg_def
  have h1 : ∀ ξ, pairingFourier μ B φ ξ = ((cQ : ℝ) : ℂ) * 𝓕⁻ g (P ξ) :=
    pairingFourier_eq μ B Q P hQP hcQ φ
  have hgi : Integrable g volume :=
    integrable_of_comp hcQ hcQ0 (by simpa [g, Function.comp_def] using hφi)
  have hcQne : ((cQ : ℝ) : ℂ) ≠ 0 := by exact_mod_cast hcQ0
  have hFg : Integrable (𝓕⁻ g) volume := by
    refine integrable_of_comp hcP hcP0 ?_
    have : (𝓕⁻ g ∘ P) = fun ξ => ((cQ : ℝ) : ℂ)⁻¹ * pairingFourier μ B φ ξ := by
      funext ξ
      rw [h1 ξ, Function.comp_apply, ← mul_assoc, inv_mul_cancel₀ hcQne, one_mul]
    rw [this]
    exact hFi.const_mul _
  have hgc : Continuous g := hφc.comp Q.symm.continuous
  have h4 : 𝓕⁻ (𝓕⁻ g) = fun z => g (-z) := by
    have e1 : 𝓕⁻ g = 𝓕 (fun z => g (-z)) := Real.fourierInv_eq_fourier_comp_neg g
    rw [e1]
    refine Continuous.fourierInv_fourier_eq (hgc.comp continuous_neg) hgi.comp_neg ?_
    rw [← e1]
    exact hFg
  rw [pairingFourier_eq μ B P Q hPQ hcP]
  have h2 : pairingFourier μ B φ ∘ P.symm = fun y => ((cQ : ℝ) : ℂ) * 𝓕⁻ g y := by
    funext y
    rw [Function.comp_apply, h1, ContinuousLinearEquiv.apply_symm_apply]
  rw [h2]
  have h3 : 𝓕⁻ (fun y => ((cQ : ℝ) : ℂ) * 𝓕⁻ g y) =
      fun z => ((cQ : ℝ) : ℂ) * 𝓕⁻ (𝓕⁻ g) z := by
    funext z
    simp only [Real.fourierInv_eq, Circle.smul_def, smul_eq_mul]
    rw [← integral_const_mul]
    congr 1
    funext v
    ring
  rw [h3, h4]
  simp only [g, Function.comp_apply, map_neg, ContinuousLinearEquiv.symm_apply_apply]
  ring

omit [FiniteDimensional ℝ W] in
/-- `F_B` maps Schwartz functions to Schwartz functions. -/
theorem exists_schwartz_pairingFourier (μ : Measure W) (B : W →ₗ[ℝ] W →ₗ[ℝ] ℝ)
    (P Q : W ≃L[ℝ] E) (hQP : ∀ w ξ, B w ξ = ⟪Q w, P ξ⟫) {cQ : ℝ≥0}
    (hcQ : μ.map Q = (cQ : ℝ≥0∞) • volume) (φ : SchwartzMap W ℂ) :
    ∃ ψ : SchwartzMap W ℂ, ⇑ψ = pairingFourier μ B φ := by
  refine ⟨((cQ : ℝ) : ℂ) • SchwartzMap.compCLMOfContinuousLinearEquiv ℂ P
    (𝓕⁻ (SchwartzMap.compCLMOfContinuousLinearEquiv ℂ Q.symm φ)), ?_⟩
  funext ξ
  rw [pairingFourier_eq μ B Q P hQP hcQ]
  simp [SchwartzMap.fourierInv_coe]

/-- **Schwartz stability and Fourier inversion** for a symmetric pairing with trivial kernel:
`F_B` maps Schwartz functions to Schwartz functions, and one constant `C` satisfies
`F_B F_B φ = C · φ(-·)` for every Schwartz function `φ`. -/
theorem exists_pairingFourier_inversion (μ : Measure W) [μ.IsAddHaarMeasure]
    (B : W →ₗ[ℝ] W →ₗ[ℝ] ℝ) (hsymm : ∀ w ξ, B w ξ = B ξ w)
    (hB : ∀ ξ, (∀ w, B w ξ = 0) → ξ = 0) :
    ∃ C : ℂ, ∀ φ : SchwartzMap W ℂ,
      (∃ ψ : SchwartzMap W ℂ, ⇑ψ = pairingFourier μ B φ) ∧
        ∀ x, pairingFourier μ B (pairingFourier μ B φ) x = C * φ (-x) := by
  let E' := EuclideanSpace ℝ (Fin (finrank ℝ W))
  let P : W ≃L[ℝ] E' := ContinuousLinearEquiv.ofFinrankEq (by simp [E'])
  obtain ⟨Q, hPQ⟩ := exists_inner_eq B hB P
  obtain ⟨cP, hcP0, hcP⟩ := exists_map_eq_smul_volume μ P
  obtain ⟨cQ, hcQ0, hcQ⟩ := exists_map_eq_smul_volume μ Q
  have hQP : ∀ w ξ, B w ξ = ⟪Q w, P ξ⟫ := fun w ξ => by rw [hsymm, hPQ, real_inner_comm]
  refine ⟨((cP : ℝ) : ℂ) * ((cQ : ℝ) : ℂ), fun φ => ?_⟩
  obtain ⟨ψ, hψ⟩ := exists_schwartz_pairingFourier μ B P Q hQP hcQ φ
  refine ⟨⟨ψ, hψ⟩, fun x => ?_⟩
  refine pairingFourier_pairingFourier μ B hsymm P Q hPQ hcP hcQ hcP0 hcQ0 φ.continuous
    (φ.integrable) ?_ x
  rw [← hψ]
  exact ψ.integrable

end Generic

end Langlands.Global.RankinSelbergGlobal.SchwartzBruhatProof
