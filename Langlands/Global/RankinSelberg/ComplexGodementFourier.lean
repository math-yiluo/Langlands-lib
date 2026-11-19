import Langlands.Global.RankinSelberg.ArchimedeanIntegrals
import Langlands.Global.RankinSelberg.SchwartzBruhatProof.ArchFourier
import Langlands.Group.GL.Maps
import Mathlib.MeasureTheory.Measure.Lebesgue.Complex
import Mathlib.MeasureTheory.Measure.Lebesgue.EqHaar
import Mathlib.Analysis.SpecialFunctions.JapaneseBracket
import Mathlib.RingTheory.Complex

/-! # Rectangular Fourier inversion at a complex place (Jacquet, Lemma 7.1)

See the paired Markdown.
-/

noncomputable section

open MeasureTheory Langlands.LocalFactor.Archimedean
open scoped FourierTransform RealInnerProductSpace NNReal ENNReal SchwartzMap

set_option autoImplicit false

namespace Langlands.Global.RankinSelbergGlobal.ComplexGodementFourier

open ArchimedeanLocal
open SchwartzBruhatProof (pairingFourier pairingFourier_pairingFourier
  exists_schwartz_pairingFourier)

/-! ### Product measures -/

section Measures

variable {ι κ : Type*} [Fintype ι] [Fintype κ] {α : Type*} [MeasurableSpace α]

/-- Uncurrying `ι → κ → α` to `ι × κ → α` preserves the product measures. -/
theorem measurePreserving_uncurry (m : Measure α) [SigmaFinite m] :
    MeasurePreserving (MeasurableEquiv.curry ι κ α).symm
      (Measure.pi fun _ : ι => Measure.pi fun _ : κ => m) (Measure.pi fun _ : ι × κ => m) := by
  refine ⟨(MeasurableEquiv.curry ι κ α).symm.measurable, ?_⟩
  refine (Measure.pi_eq fun s _ => ?_).symm
  rw [MeasurableEquiv.map_apply]
  have hpre : (MeasurableEquiv.curry ι κ α).symm ⁻¹' Set.univ.pi s =
      Set.univ.pi fun i => Set.univ.pi fun j => s (i, j) := by
    ext f
    simp [MeasurableEquiv.coe_curry_symm]
  rw [hpre, Measure.pi_pi]
  simp_rw [Measure.pi_pi]
  rw [Fintype.prod_prod_type]

/-- A constant scalar on every factor of a finite product measure. -/
theorem pi_smul_const (c : ℝ≥0) (m : Measure α) [SigmaFinite m] :
    Measure.pi (fun _ : κ => c • m) = (c ^ Fintype.card κ) • Measure.pi (fun _ : κ => m) := by
  refine Measure.pi_eq fun s _ => ?_
  rw [Measure.smul_apply, Measure.pi_pi]
  simp only [Measure.smul_apply, ENNReal.smul_def, smul_eq_mul, Finset.prod_mul_distrib,
    Finset.prod_const, Finset.card_univ, ENNReal.coe_pow]

end Measures

/-! ### Realification -/

section Realification

variable (κ : Type*) [Fintype κ]

/-- Currying as a linear equivalence. -/
def curryLinearEquiv (ι κ R M : Type*) [Semiring R] [AddCommMonoid M] [Module R M] :
    (ι × κ → M) ≃ₗ[R] (ι → κ → M) where
  toFun := Function.curry
  invFun := Function.uncurry
  map_add' _ _ := rfl
  map_smul' _ _ := rfl
  left_inv := Function.uncurry_curry
  right_inv := Function.curry_uncurry

/-- The realification `ℂ^κ ≃ ℝ^(κ × 2)`, `x ↦ (Re x_k, Im x_k)_k`, onto a Euclidean space. -/
def realify : (κ → ℂ) ≃L[ℝ] EuclideanSpace ℝ (κ × Fin 2) :=
  ((LinearEquiv.piCongrRight fun _ : κ => Complex.basisOneI.equivFun).trans
    ((curryLinearEquiv κ (Fin 2) ℝ ℝ).symm.trans
      (WithLp.linearEquiv 2 ℝ (κ × Fin 2 → ℝ)).symm)).toContinuousLinearEquiv

theorem realify_apply (x : κ → ℂ) (k : κ) (j : Fin 2) :
    realify κ x (k, j) = Complex.measurableEquivPi (x k) j := rfl

theorem measurePreserving_realify :
    MeasurePreserving (realify κ) (Measure.pi fun _ : κ => (volume : Measure ℂ)) volume := by
  have h1 : MeasurePreserving (fun (x : κ → ℂ) k => Complex.measurableEquivPi (x k))
      (Measure.pi fun _ : κ => (volume : Measure ℂ))
      (Measure.pi fun _ : κ => Measure.pi fun _ : Fin 2 => (volume : Measure ℝ)) :=
    measurePreserving_pi _ _ fun _ => Complex.volume_preserving_equiv_pi
  have h2 := measurePreserving_uncurry (ι := κ) (κ := Fin 2) (volume : Measure ℝ)
  have h3 := PiLp.volume_preserving_toLp (κ × Fin 2)
  exact h3.comp (h2.comp h1)

theorem inner_realify (x y : κ → ℂ) :
    ⟪realify κ x, realify κ y⟫ = ∑ k, ((x k).re * (y k).re + (x k).im * (y k).im) := by
  rw [PiLp.inner_apply, Fintype.sum_prod_type]
  refine Finset.sum_congr rfl fun k _ => ?_
  simp [Fin.sum_univ_two, realify_apply, mul_comm]

end Realification

/-! ### The trace pairing and the Fourier transform -/

section Fourier

variable {κ : Type*} [Fintype κ]

/-- The self-dual measure for `complexScaledCharacter a`. -/
theorem selfDual_measure (a : ℂˣ) :
    (complexSelfDualMeasure a).measure = (‖(a : ℂ)‖₊ * 2) • (volume : Measure ℂ) :=
  complexScaledMeasure_measure _ _

theorem selfDual_measure_neg (a : ℂˣ) :
    (complexSelfDualMeasure (-a)).measure = (complexSelfDualMeasure a).measure := by
  rw [selfDual_measure, selfDual_measure, Units.val_neg, nnnorm_neg]

variable (κ) in
/-- The product of the self-dual measures on `ℂ^κ`. -/
def piMeasure (a : ℂˣ) : Measure (κ → ℂ) :=
  Measure.pi fun _ : κ => (complexSelfDualMeasure a).measure

instance isAddHaarMeasure_piMeasure (a : ℂˣ) : (piMeasure κ a).IsAddHaarMeasure := by
  unfold piMeasure
  infer_instance

theorem piMeasure_neg (a : ℂˣ) : piMeasure κ (-a) = piMeasure κ a := by
  simp only [piMeasure, selfDual_measure_neg]

/-- The real trace pairing `(w, ξ) ↦ Tr(a ∑ w_k ξ_k)`. -/
def pairing (a : ℂˣ) : (κ → ℂ) →ₗ[ℝ] (κ → ℂ) →ₗ[ℝ] ℝ :=
  LinearMap.mk₂ ℝ (fun w ξ => Algebra.trace ℝ ℂ ((a : ℂ) * ∑ k, w k * ξ k))
    (fun w₁ w₂ ξ => by
      simp only [Pi.add_apply, add_mul, Finset.sum_add_distrib, mul_add, map_add])
    (fun c w ξ => by
      rw [← map_smul]
      congr 1
      simp only [Pi.smul_apply, Finset.mul_sum, Finset.smul_sum, Complex.real_smul]
      refine Finset.sum_congr rfl fun k _ => ?_
      ring)
    (fun w ξ₁ ξ₂ => by
      simp only [Pi.add_apply, mul_add, Finset.sum_add_distrib, map_add])
    (fun c w ξ => by
      rw [← map_smul]
      congr 1
      simp only [Pi.smul_apply, Finset.mul_sum, Finset.smul_sum, Complex.real_smul]
      refine Finset.sum_congr rfl fun k _ => ?_
      ring)

theorem pairing_apply (a : ℂˣ) (w ξ : κ → ℂ) :
    pairing a w ξ = Algebra.trace ℝ ℂ ((a : ℂ) * ∑ k, w k * ξ k) := rfl

theorem pairing_symm (a : ℂˣ) (w ξ : κ → ℂ) : pairing a w ξ = pairing a ξ w := by
  simp only [pairing_apply, mul_comm (w _)]

/-- The additive character `ψ_a = complexScaledCharacter a`. -/
abbrev psi (a : ℂˣ) : AddChar ℂ ℂ := (complexScaledCharacter a).complex

theorem psi_apply (a : ℂˣ) (z : ℂ) :
    psi a z = (Real.fourierChar (Algebra.trace ℝ ℂ ((a : ℂ) * z)) : ℂ) := rfl

theorem norm_psi (a : ℂˣ) (z : ℂ) : ‖psi a z‖ = 1 := by
  rw [psi_apply, Circle.norm_coe]

theorem continuous_psi (a : ℂˣ) : Continuous (psi a) :=
  HarmonicAnalysis.UnitaryAdditiveCharacter.continuous_complex _

/-- The Fourier transform on `ℂ^κ` for `ψ_a` and the self-dual product measure. -/
def fourier (a : ℂˣ) (G : (κ → ℂ) → ℂ) (ξ : κ → ℂ) : ℂ :=
  ∫ x, G x * psi a (∑ k, x k * ξ k) ∂piMeasure κ a

theorem fourier_eq_pairingFourier (a : ℂˣ) (G : (κ → ℂ) → ℂ) :
    fourier a G = pairingFourier (piMeasure κ a) (pairing a) G := rfl

/-- The scalar `z ↦ conj (2 a z)`. -/
def twist (a : ℂˣ) : ℂ ≃L[ℝ] ℂ :=
  (((LinearEquiv.smulOfNeZero ℂ ℂ (2 * (a : ℂ))
    (mul_ne_zero two_ne_zero a.ne_zero)).restrictScalars ℝ).trans
      Complex.conjCLE.toLinearEquiv).toContinuousLinearEquiv

theorem twist_apply (a : ℂˣ) (z : ℂ) : twist a z = starRingEnd ℂ (2 * (a : ℂ) * z) := by
  simp [twist, mul_assoc]

/-- The coordinatewise `twist`. -/
def twistPi (a : ℂˣ) : (κ → ℂ) ≃L[ℝ] (κ → ℂ) :=
  (LinearEquiv.piCongrRight fun _ : κ => (twist a).toLinearEquiv).toContinuousLinearEquiv

theorem twistPi_apply (a : ℂˣ) (x : κ → ℂ) (k : κ) : twistPi a x k = twist a (x k) := rfl

/-- The real-determinant factor of `twist a`. -/
def twistFactor (a : ℂˣ) : ℝ≥0 := Real.toNNReal ((‖2 * (a : ℂ)‖ ^ 2)⁻¹)

theorem map_volume_twist (a : ℂˣ) :
    (volume : Measure ℂ).map (twist a) = twistFactor a • volume := by
  have hc : (2 * (a : ℂ)) ≠ 0 := mul_ne_zero two_ne_zero a.ne_zero
  have hdet : LinearMap.det (Algebra.lmul ℝ ℂ (2 * (a : ℂ))) = ‖2 * (a : ℂ)‖ ^ 2 := by
    rw [← Algebra.norm_apply, Algebra.norm_complex_apply, Complex.normSq_eq_norm_sq]
  have hpos : 0 < ‖2 * (a : ℂ)‖ ^ 2 := pow_pos (norm_pos_iff.mpr hc) 2
  have hne : LinearMap.det (Algebra.lmul ℝ ℂ (2 * (a : ℂ))) ≠ 0 := by
    rw [hdet]; exact hpos.ne'
  have h := Measure.map_linearMap_addHaar_eq_smul_addHaar (volume : Measure ℂ) hne
  rw [hdet, abs_of_pos (inv_pos.mpr hpos)] at h
  have hf : (⇑(Algebra.lmul ℝ ℂ (2 * (a : ℂ)) : ℂ →ₗ[ℝ] ℂ)) = fun z => 2 * (a : ℂ) * z := by
    funext z
    simp
  rw [hf] at h
  have htw : (⇑(twist a)) = (starRingEnd ℂ) ∘ fun z => 2 * (a : ℂ) * z := by
    funext z
    rw [twist_apply]
    rfl
  have hconj : (volume : Measure ℂ).map (starRingEnd ℂ) = volume :=
    Complex.conjLIE.measurePreserving.map_eq
  rw [htw, ← Measure.map_map Complex.continuous_conj.measurable (by fun_prop), h,
    Measure.map_smul _ Complex.continuous_conj.aemeasurable, hconj]
  rfl

theorem measurePreserving_twist (a : ℂˣ) :
    MeasurePreserving (twist a) (complexSelfDualMeasure a).measure
      (((‖(a : ℂ)‖₊ * 2) * twistFactor a) • volume) := by
  refine ⟨(twist a).continuous.measurable, ?_⟩
  rw [selfDual_measure, Measure.map_smul _ (twist a).continuous.aemeasurable, map_volume_twist,
    smul_smul]

theorem pairing_eq_inner (a : ℂˣ) (w ξ : κ → ℂ) :
    pairing a w ξ = ⟪realify κ w, realify κ (twistPi a ξ)⟫ := by
  rw [inner_realify, pairing_apply, Algebra.trace_complex_apply, Finset.mul_sum, Complex.re_sum,
    Finset.mul_sum]
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [twistPi_apply, twist_apply]
  simp only [Complex.mul_re, Complex.mul_im, Complex.conj_re, Complex.conj_im]
  norm_num
  ring

/-- The realification data for the pairing: two linear isomorphisms onto a Euclidean space with
`Tr(a ∑ w ξ) = ⟪P w, Q ξ⟫`, whose image measures have reciprocal scalars. -/
theorem exists_realification (a : ℂˣ) :
    ∃ (P Q : (κ → ℂ) ≃L[ℝ] EuclideanSpace ℝ (κ × Fin 2)) (cP cQ : ℝ≥0),
      cP ≠ 0 ∧ cQ ≠ 0 ∧ (cP : ℝ) * cQ = 1 ∧ (∀ w ξ, pairing a w ξ = ⟪P w, Q ξ⟫) ∧
      (piMeasure κ a).map P = (cP : ℝ≥0∞) • volume ∧
      (piMeasure κ a).map Q = (cQ : ℝ≥0∞) • volume := by
  have ha : 0 < ‖(a : ℂ)‖ := norm_pos_iff.mpr a.ne_zero
  set c : ℝ≥0 := ‖(a : ℂ)‖₊ * 2 with hc
  set d : ℝ≥0 := twistFactor a with hd
  have hc0 : c ≠ 0 := by
    rw [hc]; exact mul_ne_zero (nnnorm_ne_zero_iff.mpr a.ne_zero) two_ne_zero
  have hdreal : (d : ℝ) = (‖2 * (a : ℂ)‖ ^ 2)⁻¹ := by
    rw [hd, twistFactor, Real.coe_toNNReal _ (by positivity)]
  have hd0 : d ≠ 0 := by
    intro h
    have : (d : ℝ) = 0 := by rw [h]; rfl
    rw [hdreal] at this
    have : 0 < (‖2 * (a : ℂ)‖ ^ 2)⁻¹ := by
      have : 0 < ‖2 * (a : ℂ)‖ := by rw [norm_mul]; exact mul_pos (by norm_num) ha
      positivity
    linarith
  have hpi : piMeasure κ a = (c ^ Fintype.card κ) • Measure.pi fun _ : κ => (volume : Measure ℂ) := by
    rw [piMeasure, selfDual_measure, pi_smul_const]
  have hT : (piMeasure κ a).map (twistPi a) =
      ((c * d) ^ Fintype.card κ) • Measure.pi fun _ : κ => (volume : Measure ℂ) := by
    have h := measurePreserving_pi (fun _ : κ => (complexSelfDualMeasure a).measure)
      (fun _ : κ => ((c * d) • (volume : Measure ℂ))) (fun _ => measurePreserving_twist a)
    rw [← pi_smul_const]
    exact h.map_eq
  refine ⟨realify κ, (twistPi a).trans (realify κ), c ^ Fintype.card κ, (c * d) ^ Fintype.card κ,
    pow_ne_zero _ hc0, pow_ne_zero _ (mul_ne_zero hc0 hd0), ?_, fun w ξ => pairing_eq_inner a w ξ,
    ?_, ?_⟩
  · push_cast
    rw [← mul_pow, hdreal]
    have h2 : ‖2 * (a : ℂ)‖ = 2 * ‖(a : ℂ)‖ := by rw [norm_mul]; norm_num
    rw [h2, hc]
    push_cast
    have ha' := ha.ne'
    have : (‖(a : ℂ)‖ * 2) * ((‖(a : ℂ)‖ * 2) * ((2 * ‖(a : ℂ)‖) ^ 2)⁻¹) = 1 := by
      field_simp
    rw [this, one_pow]
  · rw [hpi, Measure.map_smul _ (realify κ).continuous.aemeasurable,
      (measurePreserving_realify κ).map_eq, ENNReal.smul_def]
  · have hcomp : ⇑((twistPi a).trans (realify κ)) = realify κ ∘ twistPi a := rfl
    rw [hcomp, ← Measure.map_map (realify κ).continuous.measurable
      (twistPi a).continuous.measurable, hT, Measure.map_smul _ (realify κ).continuous.aemeasurable,
      (measurePreserving_realify κ).map_eq, ENNReal.smul_def]

/-- **Fourier inversion** with the self-dual measure: `F_(-a) F_a G = G`. -/
theorem fourier_neg_fourier (a : ℂˣ) {G : (κ → ℂ) → ℂ} (hc : Continuous G)
    (hi : Integrable G (piMeasure κ a)) (hF : Integrable (fourier a G) (piMeasure κ a))
    (b : κ → ℂ) : fourier (-a) (fourier a G) b = G b := by
  obtain ⟨P, Q, cP, cQ, hcP0, hcQ0, hcc, hPQ, hcP, hcQ⟩ := exists_realification (κ := κ) a
  have key := pairingFourier_pairingFourier (piMeasure κ a) (pairing a) (pairing_symm a) P Q hPQ
    hcP hcQ hcP0 hcQ0 hc hi hF (-b)
  rw [neg_neg, ← Complex.ofReal_mul, hcc, Complex.ofReal_one, one_mul] at key
  rw [← key, fourier, piMeasure_neg]
  unfold pairingFourier
  refine integral_congr_ae (Filter.Eventually.of_forall fun ξ => ?_)
  show fourier a G ξ * psi (-a) (∑ k, ξ k * b k) = fourier a G ξ * _
  congr 1
  simp only [psi_apply, pairing_apply, Units.val_neg, Pi.neg_apply, mul_neg, Finset.sum_neg_distrib,
    neg_mul]

/-- The Fourier transform of a Schwartz function is a Schwartz function. -/
theorem exists_schwartz_fourier (a : ℂˣ) (Φ : 𝓢(κ → ℂ, ℂ)) :
    ∃ Ψ : 𝓢(κ → ℂ, ℂ), ⇑Ψ = fourier a Φ := by
  obtain ⟨P, Q, cP, cQ, _, _, _, hPQ, _, hcQ⟩ := exists_realification (κ := κ) a
  have hQP : ∀ w ξ, pairing a w ξ = ⟪Q w, P ξ⟫ := fun w ξ => by
    rw [pairing_symm, hPQ, real_inner_comm]
  exact exists_schwartz_pairingFourier (piMeasure κ a) (pairing a) P Q hQP hcQ Φ

end Fourier

/-! ### Decay and integrability of Schwartz functions -/

section Decay

variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [NormedAddCommGroup F]
  [NormedSpace ℝ F]

/-- Polynomial decay of a Schwartz function. -/
theorem schwartz_decay (Ψ : 𝓢(E, ℂ)) (k : ℕ) :
    ∃ C, 0 ≤ C ∧ ∀ w, ‖Ψ w‖ ≤ C * ((1 + ‖w‖) ^ k)⁻¹ := by
  refine ⟨2 ^ k * (Finset.Iic (k, 0)).sup (fun m => SchwartzMap.seminorm ℝ m.1 m.2) Ψ,
    mul_nonneg (by positivity) (apply_nonneg _ _), fun w => ?_⟩
  have h := SchwartzMap.one_add_le_sup_seminorm_apply (𝕜 := ℝ) (m := (k, 0)) le_rfl le_rfl Ψ w
  rw [norm_iteratedFDeriv_zero] at h
  have hpos : 0 < (1 + ‖w‖) ^ k := by positivity
  rw [← div_eq_mul_inv, le_div_iff₀ hpos, mul_comm]
  exact h

omit [NormedSpace ℝ F] in
/-- Decay of a Schwartz function along points of larger norm. -/
theorem schwartz_decay_of_le (Ψ : 𝓢(E, ℂ)) (k : ℕ) :
    ∃ C, ∀ (y : F) (w : E), ‖y‖ ≤ ‖w‖ → ‖Ψ w‖ ≤ C * ((1 + ‖y‖) ^ k)⁻¹ := by
  obtain ⟨C, hC, hΨ⟩ := schwartz_decay Ψ k
  refine ⟨C, fun y w hyw => (hΨ w).trans ?_⟩
  gcongr

variable [FiniteDimensional ℝ F] [MeasurableSpace F] [BorelSpace F]

theorem integrable_inv_one_add_norm_pow (μ : Measure F) [μ.IsAddHaarMeasure] :
    Integrable (fun y : F => ((1 + ‖y‖) ^ (Module.finrank ℝ F + 1))⁻¹) μ := by
  have h := integrable_one_add_norm (μ := μ)
    (r := ((Module.finrank ℝ F + 1 : ℕ) : ℝ)) (by push_cast; linarith)
  refine h.congr (Filter.Eventually.of_forall fun y => ?_)
  simp only
  rw [Real.rpow_neg (by positivity), Real.rpow_natCast]

/-- A function dominated by a Schwartz function along a map that does not decrease norms is
integrable for any Haar measure. -/
theorem integrable_of_norm_le_schwartz (μ : Measure F) [μ.IsAddHaarMeasure] (Ψ : 𝓢(E, ℂ))
    {f : F → ℂ} {g : F → E} (hf : AEStronglyMeasurable f μ) (hg : ∀ y, ‖y‖ ≤ ‖g y‖)
    (hfg : ∀ y, ‖f y‖ ≤ ‖Ψ (g y)‖) : Integrable f μ := by
  obtain ⟨C, hC⟩ := schwartz_decay_of_le (F := F) Ψ (Module.finrank ℝ F + 1)
  refine ((integrable_inv_one_add_norm_pow μ).const_mul C).mono' hf
    (Filter.Eventually.of_forall fun y => ?_)
  exact (hfg y).trans (hC y (g y) (hg y))

end Decay

/-! ### Splitting the coordinates -/

section Split

variable {ι : Type*} [Fintype ι] (p : ι → Prop) [DecidablePred p]

/-- Glue `x` on the coordinates satisfying `p` and `z` on the others. -/
def merge (x : {i // p i} → ℂ) (z : {i // ¬ p i} → ℂ) : ι → ℂ :=
  (MeasurableEquiv.piEquivPiSubtypeProd (fun _ : ι => ℂ) p).symm (x, z)

omit [Fintype ι] in
theorem merge_apply (x : {i // p i} → ℂ) (z : {i // ¬ p i} → ℂ) (i : ι) :
    merge p x z i = if h : p i then x ⟨i, h⟩ else z ⟨i, h⟩ := rfl

omit [Fintype ι] in
theorem merge_apply_left (x : {i // p i} → ℂ) (z : {i // ¬ p i} → ℂ) (i : {i // p i}) :
    merge p x z i = x i := by
  simp [merge_apply, i.2]

omit [Fintype ι] in
theorem merge_apply_right (x : {i // p i} → ℂ) (z : {i // ¬ p i} → ℂ) (i : {i // ¬ p i}) :
    merge p x z i = z i := by
  simp [merge_apply, i.2]

omit [Fintype ι] in
theorem continuous_merge :
    Continuous fun xz : ({i // p i} → ℂ) × ({i // ¬ p i} → ℂ) => merge p xz.1 xz.2 :=
  (Homeomorph.piEquivPiSubtypeProd p fun _ : ι => ℂ).symm.continuous

theorem norm_le_norm_merge_left (x : {i // p i} → ℂ) (z : {i // ¬ p i} → ℂ) :
    ‖x‖ ≤ ‖merge p x z‖ := by
  refine (pi_norm_le_iff_of_nonneg (norm_nonneg _)).2 fun i => ?_
  rw [← merge_apply_left p x z i]
  exact norm_le_pi_norm _ _

theorem norm_le_norm_merge_right (x : {i // p i} → ℂ) (z : {i // ¬ p i} → ℂ) :
    ‖z‖ ≤ ‖merge p x z‖ := by
  refine (pi_norm_le_iff_of_nonneg (norm_nonneg _)).2 fun i => ?_
  rw [← merge_apply_right p x z i]
  exact norm_le_pi_norm _ _

theorem norm_le_norm_merge (xz : ({i // p i} → ℂ) × ({i // ¬ p i} → ℂ)) :
    ‖xz‖ ≤ ‖merge p xz.1 xz.2‖ := by
  rw [Prod.norm_def]
  exact max_le (norm_le_norm_merge_left p _ _) (norm_le_norm_merge_right p _ _)

theorem sum_merge_mul_merge (x α : {i // p i} → ℂ) (z y : {i // ¬ p i} → ℂ) :
    ∑ k, merge p x z k * merge p α y k = ∑ k, x k * α k + ∑ k, z k * y k := by
  rw [← Fintype.sum_subtype_add_sum_subtype p]
  simp only [merge_apply_left, merge_apply_right]

/-- Integration over `ℂ^ι` as an integral over the product of the two coordinate blocks. -/
theorem integral_merge (a : ℂˣ) (f : (ι → ℂ) → ℂ) :
    ∫ xz, f (merge p xz.1 xz.2) ∂(piMeasure {i // p i} a).prod (piMeasure {i // ¬ p i} a) =
      ∫ u, f u ∂piMeasure ι a :=
  (MeasurePreserving.symm _ (measurePreserving_piEquivPiSubtypeProd
    (fun _ : ι => (complexSelfDualMeasure a).measure) p)).integral_comp' f

variable {p}

/-- **Partial Fourier inversion.** For complementary coordinate blocks, integrating `Φ` over the
`p`-block against `ψ_(-a)` equals integrating its Fourier transform for `ψ_(-a)` over the
complementary block against `ψ_a`. -/
theorem integral_merge_left_eq (a : ℂˣ) (Φ : 𝓢(ι → ℂ, ℂ)) (α : {i // p i} → ℂ)
    (β : {i // ¬ p i} → ℂ) :
    ∫ x, Φ (merge p x β) * psi (-a) (∑ k, x k * α k) ∂piMeasure _ a =
      ∫ y, fourier (-a) Φ (merge p α y) * psi a (∑ k, y k * β k) ∂piMeasure _ a := by
  set G : ({i // ¬ p i} → ℂ) → ℂ :=
    fun z => ∫ x, Φ (merge p x z) * psi (-a) (∑ k, x k * α k) ∂piMeasure _ a with hG
  -- integrability on the product
  have hprod : ∀ ζ : {i // ¬ p i} → ℂ, Integrable
      (fun xz : ({i // p i} → ℂ) × ({i // ¬ p i} → ℂ) =>
        Φ (merge p xz.1 xz.2) * (psi (-a) (∑ k, xz.1 k * α k) * psi (-a) (∑ k, xz.2 k * ζ k)))
      ((piMeasure {i // p i} a).prod (piMeasure {i // ¬ p i} a)) := by
    intro ζ
    refine integrable_of_norm_le_schwartz _ Φ (g := fun xz => merge p xz.1 xz.2) ?_
      (norm_le_norm_merge p) fun xz => ?_
    · refine Continuous.aestronglyMeasurable ?_
      have hm := continuous_merge p
      have h1 : Continuous fun xz : ({i // p i} → ℂ) × ({i // ¬ p i} → ℂ) =>
          psi (-a) (∑ k, xz.1 k * α k) :=
        (continuous_psi (-a)).comp (by fun_prop)
      have h2 : Continuous fun xz : ({i // p i} → ℂ) × ({i // ¬ p i} → ℂ) =>
          psi (-a) (∑ k, xz.2 k * ζ k) :=
        (continuous_psi (-a)).comp (by fun_prop)
      exact (Φ.continuous.comp hm).mul (h1.mul h2)
    · rw [norm_mul, norm_mul, norm_psi, norm_psi, mul_one, mul_one]
  have hprod0 := hprod 0
  simp only [Pi.zero_apply, mul_zero, Finset.sum_const_zero, AddChar.map_zero_eq_one,
    mul_one] at hprod0
  have hGi : Integrable G (piMeasure _ a) := hprod0.integral_prod_right
  have hGc : Continuous G := by
    obtain ⟨C, hC⟩ := schwartz_decay_of_le (F := {i // p i} → ℂ) Φ
      (Module.finrank ℝ ({i // p i} → ℂ) + 1)
    refine continuous_of_dominated (fun z => ?_) (fun z => Filter.Eventually.of_forall fun x => ?_)
      ((integrable_inv_one_add_norm_pow (piMeasure {i // p i} a)).const_mul C)
      (Filter.Eventually.of_forall fun x => ?_)
    · refine Continuous.aestronglyMeasurable ?_
      exact (Φ.continuous.comp ((continuous_merge p).comp (continuous_id.prodMk continuous_const))).mul
        ((continuous_psi (-a)).comp
          (by fun_prop : Continuous fun x : {i // p i} → ℂ => ∑ k, x k * α k))
    · rw [norm_mul, norm_psi, mul_one]
      exact hC x _ (norm_le_norm_merge_left p x z)
    · exact (Φ.continuous.comp ((continuous_merge p).comp
        (continuous_const.prodMk continuous_id))).mul continuous_const
  -- the Fourier transform of `Φ` along the affine slice is the Fourier transform of `G`
  have hslice : ∀ y, fourier (-a) Φ (merge p α y) = fourier (-a) G y := by
    intro y
    rw [fourier, fourier, piMeasure_neg, piMeasure_neg, ← integral_merge p a,
      integral_prod_symm _ (by simpa only [sum_merge_mul_merge, AddChar.map_add_eq_mul] using hprod y)]
    refine integral_congr_ae (Filter.Eventually.of_forall fun z => ?_)
    simp only [hG, sum_merge_mul_merge, AddChar.map_add_eq_mul, ← mul_assoc]
    exact integral_mul_const _ _
  obtain ⟨Ψ, hΨ⟩ := exists_schwartz_fourier (-a) Φ
  have hFi : Integrable (fourier (-a) G) (piMeasure _ (-a)) := by
    rw [piMeasure_neg]
    refine integrable_of_norm_le_schwartz _ Ψ (g := merge p α) ?_
      (norm_le_norm_merge_right p α) fun y => ?_
    · refine Continuous.aestronglyMeasurable ?_
      have : fourier (-a) G = fun y => Ψ (merge p α y) := by
        ext y; rw [← hslice, hΨ]
      rw [this]
      exact Ψ.continuous.comp ((continuous_merge p).comp (continuous_const.prodMk continuous_id))
    · rw [← hslice, hΨ]
  have hinv := fourier_neg_fourier (-a) hGc (by rwa [piMeasure_neg]) hFi β
  rw [neg_neg] at hinv
  show G β = _
  rw [← hinv, fourier]
  refine integral_congr_ae (Filter.Eventually.of_forall fun y => ?_)
  simp only [hslice]

end Split

/-! ### Gluing coordinate families -/

section Block

variable {κ₁ κ₂ ρ : Type*}

/-- Gluing `(v, X)` into one coordinate vector along `σ : κ₁ ⊕ κ₂ ≃ ρ`. -/
def blockEquiv (σ : κ₁ ⊕ κ₂ ≃ ρ) : ((κ₁ → ℂ) × (κ₂ → ℂ)) ≃ᵐ (ρ → ℂ) :=
  (MeasurableEquiv.sumPiEquivProdPi fun _ : κ₁ ⊕ κ₂ => ℂ).symm.trans
    (MeasurableEquiv.piCongrLeft (fun _ : ρ => ℂ) σ)

theorem blockEquiv_apply (σ : κ₁ ⊕ κ₂ ≃ ρ) (v : κ₁ → ℂ) (X : κ₂ → ℂ) (s : κ₁ ⊕ κ₂) :
    blockEquiv σ (v, X) (σ s) = Sum.elim v X s := by
  rw [blockEquiv, MeasurableEquiv.trans_apply, MeasurableEquiv.piCongrLeft_apply_apply]
  cases s <;> rfl

variable [Fintype κ₁] [Fintype κ₂] [Fintype ρ]

theorem measurePreserving_blockEquiv (σ : κ₁ ⊕ κ₂ ≃ ρ) (a : ℂˣ) :
    MeasurePreserving (blockEquiv σ) ((piMeasure κ₁ a).prod (piMeasure κ₂ a)) (piMeasure ρ a) :=
  (measurePreserving_piCongrLeft (fun _ : ρ => (complexSelfDualMeasure a).measure) σ).comp
    (MeasurePreserving.symm _
      (measurePreserving_sumPiEquivProdPi fun _ : κ₁ ⊕ κ₂ => (complexSelfDualMeasure a).measure))

theorem integral_blockEquiv (σ : κ₁ ⊕ κ₂ ≃ ρ) (a : ℂˣ) (g : (ρ → ℂ) → ℂ) :
    ∫ vX, g (blockEquiv σ vX) ∂(piMeasure κ₁ a).prod (piMeasure κ₂ a) = ∫ x, g x ∂piMeasure ρ a :=
  (measurePreserving_blockEquiv σ a).integral_comp' g

theorem sum_blockEquiv (σ : κ₁ ⊕ κ₂ ≃ ρ) (v : κ₁ → ℂ) (X : κ₂ → ℂ) (c : ρ → ℂ) :
    ∑ q, blockEquiv σ (v, X) q * c q =
      ∑ t, v t * c (σ (.inl t)) + ∑ i, X i * c (σ (.inr i)) := by
  rw [← σ.sum_comp, Fintype.sum_sum_type]
  simp only [blockEquiv_apply, Sum.elim_inl, Sum.elim_inr]

end Block

/-! ### Rectangular matrices and the long Weyl element -/

section Matrices

/-- The Fourier transform on `k × l` complex matrices for `ψ_a`, with the self-dual product
measure and the trace pairing `(X, Y) ↦ Σ_(i,j) X_ij Y_ij`. -/
def rectFourier (a : ℂˣ) {k l : ℕ} (Φ : Matrix (Fin k) (Fin l) ℂ → ℂ)
    (Y : Matrix (Fin k) (Fin l) ℂ) : ℂ :=
  ∫ X, Φ X * psi a (∑ i, ∑ j, X i j * Y i j) ∂RankinSelberg.rectangularMeasure
    (complexSelfDualMeasure a) k l

/-- A matrix as a function on index pairs. -/
def flatM {k l : ℕ} (M : Matrix (Fin k) (Fin l) ℂ) : Fin k × Fin l → ℂ := fun q => M q.1 q.2

theorem flatM_apply {k l : ℕ} (M : Matrix (Fin k) (Fin l) ℂ) (q : Fin k × Fin l) :
    flatM M q = M q.1 q.2 := rfl

theorem curry_flatM {k l : ℕ} (M : Matrix (Fin k) (Fin l) ℂ) : Function.curry (flatM M) = M :=
  rfl

/-- Right multiplication by the long Weyl element reverses the columns. -/
theorem mul_weylLong_apply {m : ℕ} {α : Type*} (M : Matrix α (Fin m) ℂ) (b : α) (j : Fin m) :
    (M * (GeneralLinear.weylLong m ℂ).val) b j = M b j.rev := by
  rw [Matrix.mul_apply]
  simp only [GeneralLinear.weylLong_entry, mul_ite, mul_one, mul_zero]
  rw [Finset.sum_eq_single j.rev]
  · simp
  · intro l _ hl
    rw [ite_eq_right_iff]
    intro he
    exact absurd he.symm hl
  · simp

/-- Left multiplication by the long Weyl element reverses the rows. -/
theorem weylLong_mul_apply {m : ℕ} {α : Type*} (M : Matrix (Fin m) α ℂ) (i : Fin m) (b : α) :
    ((GeneralLinear.weylLong m ℂ).val * M) i b = M i.rev b := by
  rw [Matrix.mul_apply]
  simp only [GeneralLinear.weylLong_entry, ite_mul, one_mul, zero_mul]
  rw [Finset.sum_eq_single i.rev]
  · simp
  · intro l _ hl
    rw [ite_eq_right_iff]
    intro he
    exact absurd (by rw [← he, Fin.rev_rev]) hl
  · simp

end Matrices

/-! ### Jacquet's Lemma 7.1 at a complex place -/

section Jacquet

variable (n : ℕ)

/-- The strictly upper triangular positions of an `(n+1) × (n+1)` matrix. -/
abbrev Upper := {q : Fin (n + 1) × Fin (n + 1) // q.1 < q.2}

/-- The positions `(i, j)` of an `(n+1) × (n+2)` matrix with `i + j < n + 1`. -/
def lowerPos (q : Fin (n + 1) × Fin (n + 2)) : Prop := q.1.val + q.2.val < n + 1

instance (q : Fin (n + 1) × Fin (n + 2)) : Decidable (lowerPos n q) :=
  inferInstanceAs (Decidable (_ < _))

/-- The upper unipotent matrix with entries `v` above the diagonal. -/
def unip (v : Upper n → ℂ) : Matrix (Fin (n + 1)) (Fin (n + 1)) ℂ :=
  fun i j => if h : i < j then v ⟨(i, j), h⟩ else if i = j then 1 else 0

/-- `A(v, X) = [v, X]`: the unipotent matrix of `v` followed by the column `X`. -/
def blockA (v : Upper n → ℂ) (X : Fin (n + 1) → ℂ) : Matrix (Fin (n + 1)) (Fin (n + 2)) ℂ :=
  fun i j => Fin.lastCases (X i) (fun j' => unip n v i j') j

/-- `S(v, X) = Σ_i v_(i,i+1) + X_last`. -/
def superdiagSum (v : Upper n → ℂ) (X : Fin (n + 1) → ℂ) : ℂ :=
  ∑ i : Fin n, v ⟨(i.castSucc, i.succ), by simp⟩ + X (Fin.last n)

/-- The free coordinates of `A(v, X) w_(n+2)`: the positions `i + j < n + 1`. -/
def sigmaL : Upper n ⊕ Fin (n + 1) ≃ {q // lowerPos n q} where
  toFun s := match s with
    | .inl t => ⟨(t.1.1, ⟨n + 1 - t.1.2.val, by omega⟩), by
        have h := t.2
        rw [Fin.lt_def] at h
        simp only [lowerPos]
        omega⟩
    | .inr i => ⟨(i, 0), by simp only [lowerPos, Fin.val_zero]; omega⟩
  invFun q := if h : q.1.2.val = 0 then .inr q.1.1 else
    .inl ⟨(q.1.1, ⟨n + 1 - q.1.2.val, by omega⟩), by
      have h' := q.2
      simp only [lowerPos] at h'
      rw [Fin.lt_def]
      simp only
      omega⟩
  left_inv s := by
    rcases s with t | i
    · have h := t.2
      rw [Fin.lt_def] at h
      simp only
      rw [dif_neg (by omega)]
      congr 1
      apply Subtype.ext
      apply Prod.ext
      · rfl
      · apply Fin.ext
        simp only
        omega
    · simp
  right_inv q := by
    by_cases h : q.1.2.val = 0
    · simp only [h, dite_true]
      apply Subtype.ext
      apply Prod.ext
      · rfl
      · exact (Fin.ext h).symm
    · simp only [h, dite_false]
      have := q.1.2.isLt
      apply Subtype.ext
      apply Prod.ext
      · rfl
      · apply Fin.ext
        simp only
        omega

/-- The free coordinates of `w_(n+1) A(v, X)`: the positions `i + j ≥ n + 1`. -/
def sigmaR : Upper n ⊕ Fin (n + 1) ≃ {q // ¬ lowerPos n q} where
  toFun s := match s with
    | .inl t => ⟨(⟨n - t.1.1.val, by omega⟩, ⟨t.1.2.val, by omega⟩), by
        have h := t.2
        rw [Fin.lt_def] at h
        simp only [lowerPos]
        omega⟩
    | .inr i => ⟨(⟨n - i.val, by omega⟩, Fin.last (n + 1)), by
        simp only [lowerPos, Fin.val_last]
        omega⟩
  invFun q := if h : q.1.2.val = n + 1 then .inr ⟨n - q.1.1.val, by omega⟩ else
    .inl ⟨(⟨n - q.1.1.val, by omega⟩, ⟨q.1.2.val, by have := q.1.2.isLt; omega⟩), by
      have h' := q.2
      simp only [lowerPos] at h'
      rw [Fin.lt_def]
      simp only
      omega⟩
  left_inv s := by
    rcases s with t | i
    · have h := t.2
      have h1 := t.1.1.isLt
      rw [Fin.lt_def] at h
      simp only
      rw [dif_neg (by omega)]
      congr 1
      apply Subtype.ext
      apply Prod.ext
      · apply Fin.ext
        simp only
        omega
      · rfl
    · have h1 := i.isLt
      simp only [Fin.val_last, dite_true]
      congr 1
      apply Fin.ext
      simp only
      omega
  right_inv q := by
    have := q.1.1.isLt
    have := q.1.2.isLt
    by_cases h : q.1.2.val = n + 1
    · simp only [h, dite_true]
      apply Subtype.ext
      apply Prod.ext
      · apply Fin.ext
        simp only
        omega
      · apply Fin.ext
        simp only [Fin.val_last]
        omega
    · simp only [h, dite_false]
      apply Subtype.ext
      apply Prod.ext
      · apply Fin.ext
        simp only
        omega
      · rfl

/-- The indicator of the anti-diagonal `i + j = n` on the free block of `A w_(n+2)`. -/
def alphaL (q : {q // lowerPos n q}) : ℂ := if q.1.1.val + q.1.2.val = n then 1 else 0

/-- The indicator of the anti-diagonal `i + j = n + 1` on the complementary block. -/
def betaR (q : {q // ¬ lowerPos n q}) : ℂ := if q.1.1.val + q.1.2.val = n + 1 then 1 else 0

variable {n}

theorem sum_upper_superdiag (v c : Upper n → ℂ)
    (hc : ∀ t : Upper n, c t = if t.1.2.val = t.1.1.val + 1 then 1 else 0) :
    ∑ t, v t * c t = ∑ i : Fin n, v ⟨(i.castSucc, i.succ), by simp⟩ := by
  symm
  refine Fintype.sum_of_injective (fun i : Fin n => (⟨(i.castSucc, i.succ), by simp⟩ : Upper n))
    (fun i j h => ?_) _ _ (fun t ht => ?_) (fun i => ?_)
  · have := congrArg (fun t : Upper n => t.1.1.val) h
    simp only [Fin.val_castSucc] at this
    exact Fin.ext this
  · rw [hc, if_neg, mul_zero]
    intro h
    apply ht
    have h1 := t.1.2.isLt
    refine ⟨⟨t.1.1.val, by omega⟩, ?_⟩
    ext <;> simp [h]
  · rw [hc, if_pos (by simp), mul_one]

theorem sum_fin_last (X : Fin (n + 1) → ℂ) (c : Fin (n + 1) → ℂ)
    (hc : ∀ i : Fin (n + 1), c i = if i.val = n then 1 else 0) :
    ∑ i, X i * c i = X (Fin.last n) := by
  rw [Finset.sum_eq_single (Fin.last n)]
  · rw [hc, if_pos (by simp), mul_one]
  · intro i _ hi
    rw [hc, if_neg, mul_zero]
    intro h
    exact hi (Fin.ext (by simp [h]))
  · simp

theorem superdiagSum_eq_left (v : Upper n → ℂ) (X : Fin (n + 1) → ℂ) :
    superdiagSum n v X = ∑ q, blockEquiv (sigmaL n) (v, X) q * alphaL n q := by
  rw [sum_blockEquiv, superdiagSum, sum_upper_superdiag, sum_fin_last]
  · intro i
    simp [alphaL, sigmaL]
  · intro t
    have h := t.2
    have h2 := t.1.2.isLt
    rw [Fin.lt_def] at h
    show (if t.1.1.val + (n + 1 - t.1.2.val) = n then (1 : ℂ) else 0) = _
    exact if_congr ⟨fun _ => by omega, fun _ => by omega⟩ rfl rfl

theorem superdiagSum_eq_right (v : Upper n → ℂ) (X : Fin (n + 1) → ℂ) :
    superdiagSum n v X = ∑ q, blockEquiv (sigmaR n) (v, X) q * betaR n q := by
  rw [sum_blockEquiv, superdiagSum, sum_upper_superdiag, sum_fin_last]
  · intro i
    have h1 := i.isLt
    show (if (n - i.val) + (Fin.last (n + 1)).val = n + 1 then (1 : ℂ) else 0) = _
    rw [Fin.val_last]
    exact if_congr ⟨fun _ => by omega, fun _ => by omega⟩ rfl rfl
  · intro t
    have h := t.2
    have h1 := t.1.1.isLt
    have h2 := t.1.2.isLt
    rw [Fin.lt_def] at h
    show (if (n - t.1.1.val) + t.1.2.val = n + 1 then (1 : ℂ) else 0) = _
    exact if_congr ⟨fun _ => by omega, fun _ => by omega⟩ rfl rfl

theorem unip_apply (v : Upper n → ℂ) (i j : Fin (n + 1)) :
    unip n v i j = if h : i < j then v ⟨(i, j), h⟩ else if i = j then 1 else 0 := rfl

theorem blockA_of_val (v : Upper n → ℂ) (X : Fin (n + 1) → ℂ) (i : Fin (n + 1)) (j : Fin (n + 2))
    (k : Fin (n + 1)) (h : j.val = k.val) : blockA n v X i j = unip n v i k := by
  have : j = k.castSucc := Fin.ext (by simp [h])
  rw [this, blockA, Fin.lastCases_castSucc]

theorem blockA_of_val_last (v : Upper n → ℂ) (X : Fin (n + 1) → ℂ) (i : Fin (n + 1))
    (j : Fin (n + 2)) (h : j.val = n + 1) : blockA n v X i j = X i := by
  have : j = Fin.last (n + 1) := Fin.ext (by simp [h])
  rw [this, blockA, Fin.lastCases_last]

/-- `A(v, X) w_(n+2)` is the gluing of `(v, X)` on the block `i + j < n + 1` with the fixed
anti-diagonal values on the complementary block. -/
theorem flatM_blockA_mul_weylLong (v : Upper n → ℂ) (X : Fin (n + 1) → ℂ) :
    flatM (blockA n v X * (GeneralLinear.weylLong (n + 2) ℂ).val) =
      merge (lowerPos n) (blockEquiv (sigmaL n) (v, X)) (betaR n) := by
  funext q
  rw [merge_apply]
  split_ifs with hq
  · obtain ⟨s, hs⟩ := (sigmaL n).surjective ⟨q, hq⟩
    have hq' : q = ((sigmaL n) s).1 := by rw [hs]
    have hs' : (⟨q, hq⟩ : {q // lowerPos n q}) = (sigmaL n) s := hs.symm
    rw [hs', blockEquiv_apply, hq']
    rcases s with t | i
    · have h := t.2
      have h2 := t.1.2.isLt
      rw [Fin.lt_def] at h
      simp only [flatM_apply, sigmaL, Equiv.coe_fn_mk, Sum.elim_inl,
        mul_weylLong_apply]
      rw [blockA_of_val v X _ _ t.1.2 (by simp; omega), unip_apply, dif_pos t.2]
    · simp only [flatM_apply, sigmaL, Equiv.coe_fn_mk, Sum.elim_inr,
        mul_weylLong_apply]
      rw [blockA_of_val_last v X _ _ (by simp)]
  · obtain ⟨i, j⟩ := q
    simp only [lowerPos, not_lt] at hq
    have hj := j.isLt
    have hi := i.isLt
    simp only [flatM_apply, mul_weylLong_apply, betaR]
    rw [blockA_of_val v X i j.rev ⟨n + 1 - j.val, by omega⟩ (by simp), unip_apply,
      dif_neg (by rw [Fin.lt_def]; simp only; omega)]
    by_cases hij : i.val + j.val = n + 1
    · rw [if_pos (Fin.ext (by simp only; omega)), if_pos hij]
    · rw [if_neg (fun h => hij (by have := congrArg Fin.val h; simp only at this; omega)),
        if_neg hij]

/-- `w_(n+1) A(v, X)` is the gluing of the fixed anti-diagonal values on the block `i + j < n + 1`
with `(v, X)` on the complementary block. -/
theorem flatM_weylLong_mul_blockA (v : Upper n → ℂ) (X : Fin (n + 1) → ℂ) :
    flatM ((GeneralLinear.weylLong (n + 1) ℂ).val * blockA n v X) =
      merge (lowerPos n) (alphaL n) (blockEquiv (sigmaR n) (v, X)) := by
  funext q
  rw [merge_apply]
  split_ifs with hq
  · obtain ⟨i, j⟩ := q
    simp only [lowerPos] at hq
    have hi := i.isLt
    simp only [flatM_apply, weylLong_mul_apply, alphaL]
    rw [blockA_of_val v X i.rev j ⟨j.val, by omega⟩ rfl, unip_apply,
      dif_neg (by rw [Fin.lt_def]; simp only [Fin.val_rev]; omega)]
    by_cases hij : i.val + j.val = n
    · rw [if_pos (Fin.ext (by simp only [Fin.val_rev]; omega)), if_pos hij]
    · rw [if_neg (fun h => hij (by
          have := congrArg Fin.val h
          simp only [Fin.val_rev] at this
          omega)), if_neg hij]
  · obtain ⟨s, hs⟩ := (sigmaR n).surjective ⟨q, hq⟩
    have hq' : q = ((sigmaR n) s).1 := by rw [hs]
    have hs' : (⟨q, hq⟩ : {q // ¬ lowerPos n q}) = (sigmaR n) s := hs.symm
    rw [hs', blockEquiv_apply, hq']
    rcases s with t | i
    · have h := t.2
      have h1 := t.1.1.isLt
      have h2 := t.1.2.isLt
      rw [Fin.lt_def] at h
      simp only [flatM_apply, sigmaR, Equiv.coe_fn_mk, Sum.elim_inl,
        weylLong_mul_apply]
      have hrev : (⟨n - t.1.1.val, by omega⟩ : Fin (n + 1)).rev = t.1.1 :=
        Fin.ext (by simp only [Fin.val_rev]; omega)
      rw [hrev, blockA_of_val v X _ _ t.1.2 rfl, unip_apply, dif_pos t.2]
    · have h1 := i.isLt
      simp only [flatM_apply, sigmaR, Equiv.coe_fn_mk, Sum.elim_inr,
        weylLong_mul_apply]
      have hrev : (⟨n - i.val, by omega⟩ : Fin (n + 1)).rev = i :=
        Fin.ext (by simp only [Fin.val_rev]; omega)
      rw [hrev, blockA_of_val_last v X _ _ (by simp)]

/-- Currying `ℂ^((n+1) × (n+2))` to matrices, as a continuous real-linear equivalence. -/
def curryCLE : (Fin (n + 1) × Fin (n + 2) → ℂ) ≃L[ℝ] (Fin (n + 1) → Fin (n + 2) → ℂ) :=
  (curryLinearEquiv (Fin (n + 1)) (Fin (n + 2)) ℝ ℂ).toContinuousLinearEquiv

/-- A Schwartz function on matrices as a Schwartz function on `ℂ^((n+1) × (n+2))`. -/
def flat (Φ : 𝓢(Fin (n + 1) → Fin (n + 2) → ℂ, ℂ)) : 𝓢(Fin (n + 1) × Fin (n + 2) → ℂ, ℂ) :=
  SchwartzMap.compCLMOfContinuousLinearEquiv ℝ curryCLE Φ

theorem flat_apply (Φ : 𝓢(Fin (n + 1) → Fin (n + 2) → ℂ, ℂ)) (u : Fin (n + 1) × Fin (n + 2) → ℂ) :
    flat Φ u = Φ (Function.curry u) := rfl

theorem rectFourier_eq_fourier (a : ℂˣ) (Φ : 𝓢(Fin (n + 1) → Fin (n + 2) → ℂ, ℂ))
    (Y : Matrix (Fin (n + 1)) (Fin (n + 2)) ℂ) :
    rectFourier a Φ Y = fourier a (flat Φ) (flatM Y) := by
  have h := (measurePreserving_uncurry (ι := Fin (n + 1)) (κ := Fin (n + 2))
    (complexSelfDualMeasure a).measure).integral_comp'
    (fun u => flat Φ u * psi a (∑ k, u k * flatM Y k))
  unfold rectFourier fourier piMeasure RankinSelberg.rectangularMeasure
  rw [← h]
  refine integral_congr_ae (Filter.Eventually.of_forall fun X => ?_)
  simp only [MeasurableEquiv.coe_curry_symm, flat_apply, Fintype.sum_prod_type, flatM_apply]
  rfl

/-- **Jacquet, Lemma 7.1, complex case** (`m = n + 1`). For a Schwartz function `Φ` on the
complex `(n+1) × (n+2)` matrices and `a ∈ ℂˣ`,
`∫ Φ(A(v,X) w_(n+2)) ψ_(-a)(S(v,X)) dv dX = ∫ Φ̂(w_(n+1) A(v,X)) ψ_a(S(v,X)) dv dX`,
where `Φ̂ = rectFourier (-a) Φ`, and `dv dX` is the product of the self-dual measures. -/
theorem integral_blockA_mul_weylLong_eq (a : ℂˣ) (Φ : 𝓢(Fin (n + 1) → Fin (n + 2) → ℂ, ℂ)) :
    ∫ vX, Φ (blockA n vX.1 vX.2 * (GeneralLinear.weylLong (n + 2) ℂ).val) *
        psi (-a) (superdiagSum n vX.1 vX.2) ∂(piMeasure (Upper n) a).prod
          (piMeasure (Fin (n + 1)) a) =
      ∫ vX, rectFourier (-a) Φ ((GeneralLinear.weylLong (n + 1) ℂ).val * blockA n vX.1 vX.2) *
        psi a (superdiagSum n vX.1 vX.2) ∂(piMeasure (Upper n) a).prod
          (piMeasure (Fin (n + 1)) a) := by
  have hL : ∀ vX : (Upper n → ℂ) × (Fin (n + 1) → ℂ),
      Φ (blockA n vX.1 vX.2 * (GeneralLinear.weylLong (n + 2) ℂ).val) *
        psi (-a) (superdiagSum n vX.1 vX.2) =
      (fun x => flat Φ (merge (lowerPos n) x (betaR n)) * psi (-a) (∑ k, x k * alphaL n k))
        (blockEquiv (sigmaL n) vX) := by
    rintro ⟨v, X⟩
    simp only [flat_apply, ← flatM_blockA_mul_weylLong, curry_flatM, superdiagSum_eq_left]
  have hR : ∀ vX : (Upper n → ℂ) × (Fin (n + 1) → ℂ),
      rectFourier (-a) Φ ((GeneralLinear.weylLong (n + 1) ℂ).val * blockA n vX.1 vX.2) *
        psi a (superdiagSum n vX.1 vX.2) =
      (fun y => fourier (-a) (flat Φ) (merge (lowerPos n) (alphaL n) y) *
        psi a (∑ k, y k * betaR n k)) (blockEquiv (sigmaR n) vX) := by
    rintro ⟨v, X⟩
    simp only [rectFourier_eq_fourier, ← flatM_weylLong_mul_blockA, superdiagSum_eq_right]
  simp_rw [hL, hR]
  rw [integral_blockEquiv (sigmaL n) a
      (fun x => flat Φ (merge (lowerPos n) x (betaR n)) * psi (-a) (∑ k, x k * alphaL n k)),
    integral_blockEquiv (sigmaR n) a
      (fun y => fourier (-a) (flat Φ) (merge (lowerPos n) (alphaL n) y) *
        psi a (∑ k, y k * betaR n k))]
  exact integral_merge_left_eq a (flat Φ) (alphaL n) (betaR n)

end Jacquet

/-- **Jacquet, Lemma 7.1, at a complex place**, as a proposition. For every `m = n + 1 ≥ 1`,
every `a ∈ ℂˣ` and every Schwartz function `Φ` on the complex `m × (m + 1)` matrices,
`∫ Φ(A(v,X) w_(m+1)) ψ_(-a)(S(v,X)) dv dX = ∫ Φ̂(w_m A(v,X)) ψ_a(S(v,X)) dv dX`, where
`Φ̂ = rectFourier (-a) Φ` and `dv dX` is the product of the self-dual measures for `ψ_a`. -/
def ComplexRectangularFourierInversionStatement : Prop :=
  ∀ (n : ℕ) (a : ℂˣ) (Φ : 𝓢(Fin (n + 1) → Fin (n + 2) → ℂ, ℂ)),
    ∫ vX, Φ (blockA n vX.1 vX.2 * (GeneralLinear.weylLong (n + 2) ℂ).val) *
        psi (-a) (superdiagSum n vX.1 vX.2) ∂(piMeasure (Upper n) a).prod
          (piMeasure (Fin (n + 1)) a) =
      ∫ vX, rectFourier (-a) Φ ((GeneralLinear.weylLong (n + 1) ℂ).val * blockA n vX.1 vX.2) *
        psi a (superdiagSum n vX.1 vX.2) ∂(piMeasure (Upper n) a).prod
          (piMeasure (Fin (n + 1)) a)

/-- Jacquet's Lemma 7.1 at a complex place holds. -/
theorem complexRectangularFourierInversion : ComplexRectangularFourierInversionStatement :=
  fun _ a Φ => integral_blockA_mul_weylLong_eq a Φ

end Langlands.Global.RankinSelbergGlobal.ComplexGodementFourier
