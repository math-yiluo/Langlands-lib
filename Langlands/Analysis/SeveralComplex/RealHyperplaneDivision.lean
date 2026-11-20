import Langlands.Analysis.SeveralComplex.ParametricIntegral
import Langlands.Analysis.SeveralComplex.RealSliceIdentity
import Langlands.Analysis.SeveralComplex.SquareIntegrableDivision
import Langlands.Analysis.SeveralComplex.LineIntegrability
import Mathlib.GroupTheory.CosetCover

/-! # Division by products of real linear forms

Let `Q s = ∏ β ∈ S, ℓ β (s - s₀) ^ m` be a product of powers of nonzero complex linear forms on
`ℂⁿ` that are real on `ℝⁿ`. If a holomorphic function `H` near `s₀` has `H / Q` square integrable
on the totally real slice `s₀ + iℝⁿ` near `s₀`, then `Q` divides `H` near `s₀`; the quotient is
an explicit Cauchy integral along a generic real direction. Divisibility persists under locally
uniform limits of such functions. -/

noncomputable section
set_option autoImplicit false

namespace Langlands.Analysis.SeveralComplex

open MeasureTheory Metric Filter Topology Set Real

variable {n : ℕ} {ι : Type*}

/-- The complex vector with the same coordinates as a real vector. -/
def ofRealVec (x : Fin n → ℝ) : Fin n → ℂ := fun j => (x j : ℂ)

theorem norm_ofRealVec (x : Fin n → ℝ) : ‖ofRealVec x‖ = ‖x‖ := by
  apply le_antisymm
  · refine (pi_norm_le_iff_of_nonneg (norm_nonneg x)).2 fun j => ?_
    simpa [ofRealVec] using norm_le_pi_norm x j
  · refine (pi_norm_le_iff_of_nonneg (norm_nonneg _)).2 fun j => ?_
    have := norm_le_pi_norm (ofRealVec x) j
    simpa [ofRealVec] using this

/-- `ofRealVec` as a real-linear map. -/
def ofRealVecLm : (Fin n → ℝ) →ₗ[ℝ] (Fin n → ℂ) where
  toFun := ofRealVec
  map_add' x y := by ext j; simp [ofRealVec]
  map_smul' c x := by ext j; simp [ofRealVec]

theorem realSlice_sub (s₀ : Fin n → ℂ) (x : Fin n → ℝ) :
    realSlice s₀ x - s₀ = Complex.I • ofRealVec x := by
  ext j
  simp [realSlice, ofRealVec]

theorem realSlice_add_smul (s₀ : Fin n → ℂ) (x v : Fin n → ℝ) (t : ℝ) :
    realSlice s₀ x + (t : ℂ) • (Complex.I • ofRealVec v) = realSlice s₀ (x + t • v) := by
  ext j
  simp [realSlice, ofRealVec]
  ring

/-- The product `Q s = ∏ β ∈ S, ℓ β (s - s₀) ^ m`. -/
def rootProduct (S : Finset ι) (ℓ : ι → (Fin n → ℂ) →ₗ[ℂ] ℂ) (m : ℕ) (s₀ s : Fin n → ℂ) : ℂ :=
  ∏ β ∈ S, (ℓ β (s - s₀)) ^ m

theorem continuous_linearMap_apply (ℓ : (Fin n → ℂ) →ₗ[ℂ] ℂ) : Continuous fun s => ℓ s :=
  ℓ.continuous_of_finiteDimensional

theorem differentiable_linearMap_apply (ℓ : (Fin n → ℂ) →ₗ[ℂ] ℂ) : Differentiable ℂ fun s => ℓ s :=
  (LinearMap.toContinuousLinearMap ℓ).differentiable

theorem differentiable_rootProduct (S : Finset ι) (ℓ : ι → (Fin n → ℂ) →ₗ[ℂ] ℂ) (m : ℕ)
    (s₀ : Fin n → ℂ) : Differentiable ℂ (rootProduct S ℓ m s₀) := by
  classical
  show Differentiable ℂ (fun s => ∏ β ∈ S, (ℓ β (s - s₀)) ^ m)
  induction S using Finset.induction_on with
  | empty =>
    simp only [Finset.prod_empty]
    exact differentiable_const 1
  | insert β S hβ ih =>
    have h : (fun s => ∏ x ∈ insert β S, (ℓ x (s - s₀)) ^ m) =
        fun s => (ℓ β (s - s₀)) ^ m * ∏ x ∈ S, (ℓ x (s - s₀)) ^ m := by
      funext s
      rw [Finset.prod_insert hβ]
    rw [h]
    exact (((differentiable_linearMap_apply (ℓ β)).comp (differentiable_id.sub_const s₀)).pow
      m).mul ih

theorem continuous_rootProduct (S : Finset ι) (ℓ : ι → (Fin n → ℂ) →ₗ[ℂ] ℂ) (m : ℕ)
    (s₀ : Fin n → ℂ) : Continuous (rootProduct S ℓ m s₀) :=
  (differentiable_rootProduct S ℓ m s₀).continuous

/-- The real linear form `x ↦ Re ℓ (x)` on `ℝⁿ`. -/
def realPart (ℓ : (Fin n → ℂ) →ₗ[ℂ] ℂ) : (Fin n → ℝ) →ₗ[ℝ] ℝ :=
  Complex.reLm.comp ((ℓ.restrictScalars ℝ).comp ofRealVecLm)

theorem realPart_apply (ℓ : (Fin n → ℂ) →ₗ[ℂ] ℂ) (x : Fin n → ℝ) :
    realPart ℓ x = (ℓ (ofRealVec x)).re :=
  rfl

theorem eq_realPart {ℓ : (Fin n → ℂ) →ₗ[ℂ] ℂ}
    (hreal : ∀ x : Fin n → ℝ, (ℓ (fun j => (x j : ℂ))).im = 0) (x : Fin n → ℝ) :
    ℓ (ofRealVec x) = (realPart ℓ x : ℂ) := by
  apply Complex.ext
  · simp [realPart_apply]
  · rw [Complex.ofReal_im]
    exact hreal x

/-- A nonzero complex linear form that is real on `ℝⁿ` has nonzero real part. -/
theorem realPart_ne_zero {ℓ : (Fin n → ℂ) →ₗ[ℂ] ℂ} (hℓ : ℓ ≠ 0)
    (hreal : ∀ x : Fin n → ℝ, (ℓ (fun j => (x j : ℂ))).im = 0) : realPart ℓ ≠ 0 := by
  intro h0
  apply hℓ
  refine LinearMap.ext fun z => ?_
  have hz : z = ofRealVec (fun j => (z j).re) + Complex.I • ofRealVec (fun j => (z j).im) := by
    ext j
    simp only [ofRealVec, Pi.add_apply, Pi.smul_apply, smul_eq_mul]
    rw [mul_comm]
    exact (Complex.re_add_im _).symm
  have h1 := eq_realPart hreal (fun j => (z j).re)
  have h2 := eq_realPart hreal (fun j => (z j).im)
  rw [h0] at h1 h2
  rw [hz, map_add, map_smul, h1, h2]
  simp

/-- **A generic real direction.** For finitely many nonzero complex linear forms on `ℂⁿ⁺¹` that
are real on `ℝⁿ⁺¹`, some real `v` with `v 0 = 1` is not in the kernel of any of them. -/
theorem exists_real_direction (S : Finset ι) (ℓ : ι → (Fin (n + 1) → ℂ) →ₗ[ℂ] ℂ)
    (hℓ : ∀ β ∈ S, ℓ β ≠ 0)
    (hreal : ∀ β ∈ S, ∀ x : Fin (n + 1) → ℝ, (ℓ β (fun j => (x j : ℂ))).im = 0) :
    ∃ v : Fin (n + 1) → ℝ, v 0 = 1 ∧ ∀ β ∈ S, realPart (ℓ β) v ≠ 0 := by
  classical
  let p0 : (Fin (n + 1) → ℝ) →ₗ[ℝ] ℝ := LinearMap.proj 0
  let subs : Finset (Submodule ℝ (Fin (n + 1) → ℝ)) :=
    insert (LinearMap.ker p0) (S.image fun β => LinearMap.ker (realPart (ℓ β)))
  have htop : ⊤ ∉ subs := by
    simp only [subs, Finset.mem_insert, Finset.mem_image, not_or, not_exists, not_and]
    constructor
    · intro h
      have : (Pi.single 0 1 : Fin (n + 1) → ℝ) ∈ LinearMap.ker p0 := by rw [← h]; trivial
      simp [p0] at this
    · intro β hβ h
      exact realPart_ne_zero (hℓ β hβ) (hreal β hβ) (LinearMap.ker_eq_top.1 h)
  have hne := Subspace.biUnion_ne_univ_of_top_notMem htop
  obtain ⟨v₀, hv₀⟩ : ∃ v₀, v₀ ∉ ⋃ p ∈ subs, (p : Set (Fin (n + 1) → ℝ)) := by
    by_contra h
    simp only [not_exists, not_not] at h
    exact hne (eq_univ_of_forall h)
  simp only [mem_iUnion, SetLike.mem_coe, not_exists, subs, Finset.mem_insert,
    Finset.mem_image] at hv₀
  have h0 : v₀ 0 ≠ 0 := by
    intro h
    exact hv₀ (LinearMap.ker p0) (Or.inl rfl) (by simpa [p0] using h)
  have hβ : ∀ β ∈ S, realPart (ℓ β) v₀ ≠ 0 := by
    intro β hβ h
    exact hv₀ _ (Or.inr ⟨β, hβ, rfl⟩) h
  refine ⟨(v₀ 0)⁻¹ • v₀, by simp [h0], fun β hb => ?_⟩
  rw [map_smul, smul_eq_mul]
  exact mul_ne_zero (inv_ne_zero h0) (hβ β hb)

/-- On the line `w ↦ s₀ + i x + w (i v)` the product `Q` is a real polynomial in `w` with real
roots: `Q = c ∏ (w - τ β)` over `S × Fin m`, `τ β = -Re ℓ_β(x) / Re ℓ_β(v)`. -/
theorem rootProduct_line (S : Finset ι) (ℓ : ι → (Fin n → ℂ) →ₗ[ℂ] ℂ) (m : ℕ)
    (hreal : ∀ β ∈ S, ∀ x : Fin n → ℝ, (ℓ β (fun j => (x j : ℂ))).im = 0)
    (s₀ : Fin n → ℂ) (x v : Fin n → ℝ) (hv : ∀ β ∈ S, realPart (ℓ β) v ≠ 0) (w : ℂ) :
    rootProduct S ℓ m s₀ (realSlice s₀ x + w • (Complex.I • ofRealVec v)) =
      (∏ β ∈ S, (Complex.I * realPart (ℓ β) v) ^ m) *
        ∏ p ∈ S ×ˢ (Finset.univ : Finset (Fin m)),
          (w - ((-(realPart (ℓ p.1) x / realPart (ℓ p.1) v) : ℝ) : ℂ)) := by
  unfold rootProduct
  rw [Finset.prod_product, ← Finset.prod_mul_distrib]
  refine Finset.prod_congr rfl fun β hβ => ?_
  dsimp only
  rw [Finset.prod_const, Finset.card_univ, Fintype.card_fin, ← mul_pow]
  congr 1
  have hsub : realSlice s₀ x + w • (Complex.I • ofRealVec v) - s₀ =
      Complex.I • ofRealVec x + w • (Complex.I • ofRealVec v) := by
    rw [add_sub_right_comm, realSlice_sub]
  rw [hsub, map_add, map_smul, map_smul, map_smul, eq_realPart (hreal β hβ),
    eq_realPart (hreal β hβ)]
  have hb : (realPart (ℓ β) v : ℂ) ≠ 0 := by exact_mod_cast hv β hβ
  push_cast
  field_simp
  ring

/-- The Cauchy integral `s ↦ (2πi)⁻¹ ∮_{|z| = R} z⁻¹ H(s + z u) / Q(s + z u) dz`: the candidate
quotient `H / Q` along the direction `u`. -/
def cauchyQuotient (S : Finset ι) (ℓ : ι → (Fin n → ℂ) →ₗ[ℂ] ℂ) (m : ℕ) (s₀ u : Fin n → ℂ)
    (R : ℝ) (H : (Fin n → ℂ) → ℂ) (s : Fin n → ℂ) : ℂ :=
  (2 * π * Complex.I)⁻¹ *
    ∮ z in C(0, R), z⁻¹ * (H (s + z • u) * (rootProduct S ℓ m s₀ (s + z • u))⁻¹)

/-- The integrand of `cauchyQuotient` as a function of `(s, z)`. -/
def cauchyKernel (S : Finset ι) (ℓ : ι → (Fin n → ℂ) →ₗ[ℂ] ℂ) (m : ℕ) (s₀ u : Fin n → ℂ)
    (H : (Fin n → ℂ) → ℂ) (s : Fin n → ℂ) (z : ℂ) : ℂ :=
  z⁻¹ * (H (s + z • u) * (rootProduct S ℓ m s₀ (s + z • u))⁻¹)

/-- The integrand of `cauchyQuotient` in the angle `θ`. -/
def cauchyIntegrand (S : Finset ι) (ℓ : ι → (Fin n → ℂ) →ₗ[ℂ] ℂ) (m : ℕ) (s₀ u : Fin n → ℂ)
    (R : ℝ) (H : (Fin n → ℂ) → ℂ) (s : Fin n → ℂ) (θ : ℝ) : ℂ :=
  deriv (circleMap 0 R) θ * cauchyKernel S ℓ m s₀ u H s (circleMap 0 R θ)

theorem cauchyQuotient_eq_integral (S : Finset ι) (ℓ : ι → (Fin n → ℂ) →ₗ[ℂ] ℂ) (m : ℕ)
    (s₀ u : Fin n → ℂ) (R : ℝ) (H : (Fin n → ℂ) → ℂ) (s : Fin n → ℂ) :
    cauchyQuotient S ℓ m s₀ u R H s = (2 * π * Complex.I)⁻¹ *
      ∫ θ, cauchyIntegrand S ℓ m s₀ u R H s θ ∂(volume.restrict (Ioc 0 (2 * π))) := by
  rw [cauchyQuotient, circleIntegral, intervalIntegral.integral_of_le two_pi_pos.le]
  simp only [smul_eq_mul, cauchyIntegrand, cauchyKernel]

/-- The kernel of `cauchyQuotient` is continuous on `K × {|z| = R}`. -/
theorem continuousOn_cauchyKernel (S : Finset ι) (ℓ : ι → (Fin n → ℂ) →ₗ[ℂ] ℂ)
    (m : ℕ) (s₀ u : Fin n → ℂ) {R : ℝ} (hR : 0 < R) {H : (Fin n → ℂ) → ℂ}
    {W : Set (Fin n → ℂ)} (hH : ContinuousOn H W) {K : Set (Fin n → ℂ)}
    (h1 : ∀ s ∈ K, ∀ z ∈ sphere (0 : ℂ) R, s + z • u ∈ W)
    (h2 : ∀ s ∈ K, ∀ z ∈ sphere (0 : ℂ) R, rootProduct S ℓ m s₀ (s + z • u) ≠ 0) :
    ContinuousOn (fun p : (Fin n → ℂ) × ℂ => cauchyKernel S ℓ m s₀ u H p.1 p.2)
      (K ×ˢ sphere 0 R) := by
  have hz : ∀ p ∈ K ×ˢ sphere (0 : ℂ) R, p.2 ≠ 0 := by
    intro p hp
    have := hp.2
    rw [mem_sphere_zero_iff_norm] at this
    intro h
    rw [h, norm_zero] at this
    exact hR.ne this
  have hlin : Continuous fun p : (Fin n → ℂ) × ℂ => p.1 + p.2 • u := by fun_prop
  refine ContinuousOn.mul (continuousOn_snd.inv₀ hz) (ContinuousOn.mul ?_ ?_)
  · exact hH.comp hlin.continuousOn fun p hp => h1 p.1 hp.1 p.2 hp.2
  · exact ((continuous_rootProduct S ℓ m s₀).comp hlin).continuousOn.inv₀
      fun p hp => h2 p.1 hp.1 p.2 hp.2

set_option maxHeartbeats 2000000 in
/-- **Holomorphy of the Cauchy quotient.** -/
theorem differentiableOn_cauchyQuotient (S : Finset ι) (ℓ : ι → (Fin n → ℂ) →ₗ[ℂ] ℂ) (m : ℕ)
    (s₀ u : Fin n → ℂ) {R : ℝ} (hR : 0 < R) {H : (Fin n → ℂ) → ℂ} {W : Set (Fin n → ℂ)}
    (hW : IsOpen W) (hH : DifferentiableOn ℂ H W) {P : Set (Fin n → ℂ)} (hP : IsOpen P)
    (h1 : ∀ s ∈ P, ∀ z ∈ sphere (0 : ℂ) R, s + z • u ∈ W)
    (h2 : ∀ s ∈ P, ∀ z ∈ sphere (0 : ℂ) R, rootProduct S ℓ m s₀ (s + z • u) ≠ 0) :
    DifferentiableOn ℂ (cauchyQuotient S ℓ m s₀ u R H) P := by
  have hcirc : ∀ θ, circleMap 0 R θ ∈ sphere (0 : ℂ) R := circleMap_mem_sphere 0 hR.le
  have hcont := continuousOn_cauchyKernel S ℓ m s₀ u hR hH.continuousOn h1 h2
  have : IsFiniteMeasure (volume.restrict (Ioc (0 : ℝ) (2 * π))) :=
    isFiniteMeasure_restrict.2 measure_Ioc_lt_top.ne
  have hkernel : ∀ z ∈ sphere (0 : ℂ) R,
      DifferentiableOn ℂ (fun s => cauchyKernel S ℓ m s₀ u H s z) P := by
    intro z hz s hs
    have hHs : DifferentiableAt ℂ (fun s => H (s + z • u)) s :=
      (hH.differentiableAt (hW.mem_nhds (h1 s hs z hz))).comp s
        (differentiableAt_id.add_const _)
    have hQs : DifferentiableAt ℂ (fun s => rootProduct S ℓ m s₀ (s + z • u)) s :=
      (differentiable_rootProduct S ℓ m s₀ _).comp s (differentiableAt_id.add_const _)
    exact ((hHs.mul (hQs.inv (h2 s hs z hz))).const_mul z⁻¹).differentiableWithinAt
  have hint : DifferentiableOn ℂ
      (fun s => ∫ θ, cauchyIntegrand S ℓ m s₀ u R H s θ ∂(volume.restrict (Ioc 0 (2 * π)))) P := by
    refine differentiableOn_integral_of_bounded (volume.restrict (Ioc 0 (2 * π)))
      (cauchyIntegrand S ℓ m s₀ u R H) hP (fun θ => ?_) (fun s hs => ?_) (fun K hKP hK => ?_)
    · show DifferentiableOn ℂ (fun s => deriv (circleMap 0 R) θ *
        cauchyKernel S ℓ m s₀ u H s (circleMap 0 R θ)) P
      exact (hkernel _ (hcirc θ)).const_mul (deriv (circleMap 0 R) θ)
    · have hgs : ContinuousOn (fun z => cauchyKernel S ℓ m s₀ u H s z) (sphere 0 R) := by
        refine hcont.comp (continuous_const.prodMk continuous_id).continuousOn ?_
        intro z hz
        exact ⟨hs, hz⟩
      have hF : Continuous (cauchyIntegrand S ℓ m s₀ u R H s) := by
        refine Continuous.mul ?_ (hgs.comp_continuous (continuous_circleMap 0 R) hcirc)
        rw [funext (deriv_circleMap 0 R)]
        fun_prop
      exact hF.aestronglyMeasurable
    · obtain ⟨C, hC⟩ := (hK.prod (isCompact_sphere 0 R)).exists_bound_of_continuousOn
        (hcont.mono (prod_mono hKP subset_rfl))
      refine ⟨R * C, fun s hs θ => ?_⟩
      have hb := hC (s, circleMap 0 R θ) ⟨hs, hcirc θ⟩
      have hF : ‖cauchyIntegrand S ℓ m s₀ u R H s θ‖ =
          R * ‖cauchyKernel S ℓ m s₀ u H s (circleMap 0 R θ)‖ := by
        rw [cauchyIntegrand, norm_mul, deriv_circleMap, norm_mul, Complex.norm_I, mul_one,
          norm_circleMap_zero, abs_of_pos hR]
      rw [hF]
      exact mul_le_mul_of_nonneg_left hb hR.le
  have hfun : cauchyQuotient S ℓ m s₀ u R H = fun s => (2 * π * Complex.I)⁻¹ *
      ∫ θ, cauchyIntegrand S ℓ m s₀ u R H s θ ∂(volume.restrict (Ioc 0 (2 * π))) :=
    funext (cauchyQuotient_eq_integral S ℓ m s₀ u R H)
  rw [hfun]
  exact hint.const_mul _

/-- **Division along a good line.** Let `s = s₀ + i x` with `x` real and `u = i v`. If `H` is
holomorphic near the disc `{s + z u : |z| < 2R}`, `Q (s + z u) ≠ 0` for `|z| = R`, the roots
`τ β = -Re ℓ_β(x)/Re ℓ_β(v)` satisfy `|τ β| < T ≤ 2R`, and `t ↦ H/Q (s₀ + i(x + t v))` is square
integrable on `(-T, T)`, then `H s = Q s · cauchyQuotient H s`. -/
theorem eq_mul_cauchyQuotient_of_line (S : Finset ι) (ℓ : ι → (Fin n → ℂ) →ₗ[ℂ] ℂ) (m : ℕ)
    (hreal : ∀ β ∈ S, ∀ x : Fin n → ℝ, (ℓ β (fun j => (x j : ℂ))).im = 0)
    (s₀ : Fin n → ℂ) (v : Fin n → ℝ) (hv : ∀ β ∈ S, realPart (ℓ β) v ≠ 0) {R T : ℝ}
    (hR : 0 < R) (hTR : T ≤ 2 * R) {H : (Fin n → ℂ) → ℂ} {W : Set (Fin n → ℂ)} (hW : IsOpen W)
    (hH : DifferentiableOn ℂ H W) (x : Fin n → ℝ)
    (h1 : ∀ z ∈ ball (0 : ℂ) (2 * R), realSlice s₀ x + z • (Complex.I • ofRealVec v) ∈ W)
    (h2 : ∀ z ∈ sphere (0 : ℂ) R,
      rootProduct S ℓ m s₀ (realSlice s₀ x + z • (Complex.I • ofRealVec v)) ≠ 0)
    (h3 : ∀ β ∈ S, |realPart (ℓ β) x / realPart (ℓ β) v| < T)
    (hgood : IntegrableOn (fun t : ℝ => ‖H (realSlice s₀ (x + t • v)) /
      rootProduct S ℓ m s₀ (realSlice s₀ (x + t • v))‖ ^ 2) (Ioo (-T) T)) :
    H (realSlice s₀ x) = rootProduct S ℓ m s₀ (realSlice s₀ x) *
      cauchyQuotient S ℓ m s₀ (Complex.I • ofRealVec v) R H (realSlice s₀ x) := by
  set Q := rootProduct S ℓ m s₀ with hQ
  set u : Fin n → ℂ := Complex.I • ofRealVec v with hu
  set s := realSlice s₀ x with hs
  set c : ℂ := ∏ β ∈ S, (Complex.I * realPart (ℓ β) v) ^ m with hc
  set τ : ι × Fin m → ℝ := fun p => -(realPart (ℓ p.1) x / realPart (ℓ p.1) v) with hτ
  have hc0 : c ≠ 0 := by
    rw [hc, Finset.prod_ne_zero_iff]
    intro β hβ
    exact pow_ne_zero _ (mul_ne_zero Complex.I_ne_zero (by exact_mod_cast hv β hβ))
  have hline : ∀ z : ℂ, Q (s + z • u) = c * ∏ p ∈ S ×ˢ (Finset.univ : Finset (Fin m)),
      (z - (τ p : ℂ)) := fun z => rootProduct_line S ℓ m hreal s₀ x v hv z
  let f : ℂ → ℂ := fun z => H (s + z • u)
  have hf : DifferentiableOn ℂ f (ball 0 (2 * R)) := by
    intro z hz
    have : DifferentiableAt ℂ f z :=
      (hH.differentiableAt (hW.mem_nhds (h1 z hz))).comp z
        ((differentiableAt_id.smul_const u).const_add s)
    exact this.differentiableWithinAt
  have hτT : ∀ p ∈ S ×ˢ (Finset.univ : Finset (Fin m)), |τ p| < T := by
    intro p hp
    simp only [hτ, abs_neg]
    exact h3 p.1 (Finset.mem_product.1 hp).1
  have hint : IntegrableOn (fun t : ℝ => ‖f t / (c * ∏ p ∈ S ×ˢ (Finset.univ : Finset (Fin m)),
      ((t : ℂ) - τ p))‖ ^ 2) (Ioo (-T) T) := by
    refine hgood.congr_fun (fun t _ => ?_) measurableSet_Ioo
    simp only [f, ← hline, hs, hu, realSlice_add_smul]
  obtain ⟨φ, hφ, hfφ⟩ := exists_eq_mul_prod_of_integrableOn _ τ hc0 hTR hτT hf hint
  have hRR : R < 2 * R := by linarith
  have hcl : closedBall (0 : ℂ) R ⊆ ball 0 (2 * R) := closedBall_subset_ball hRR
  have hdiff : DiffContOnCl ℂ φ (ball 0 R) := by
    apply DifferentiableOn.diffContOnCl
    rw [closure_ball 0 hR.ne']
    exact hφ.mono hcl
  have hcauchy := hdiff.two_pi_i_inv_smul_circleIntegral_sub_inv_smul (mem_ball_self hR)
  have hcongr : (∮ z in C(0, R), z⁻¹ * (H (s + z • u) * (Q (s + z • u))⁻¹)) =
      ∮ z in C(0, R), (z - 0)⁻¹ • φ z := by
    refine circleIntegral.integral_congr hR.le fun z hz => ?_
    have hzb : z ∈ ball (0 : ℂ) (2 * R) := hcl (sphere_subset_closedBall hz)
    have hQz : Q (s + z • u) ≠ 0 := h2 z hz
    simp only [sub_zero]
    congr 1
    have h := hfφ z hzb
    simp only [f] at h
    rw [h, ← hline z]
    field_simp
  have hq : cauchyQuotient S ℓ m s₀ u R H s = φ 0 := by
    rw [cauchyQuotient, ← hQ, hcongr, ← smul_eq_mul, hcauchy]
  have h0 := hfφ 0 (mem_ball_self (by linarith))
  simp only [f, zero_smul, add_zero] at h0
  rw [hq, h0]
  have := hline 0
  simp only [zero_smul, add_zero] at this
  rw [this]

theorem continuous_realSlice (s₀ : Fin n → ℂ) : Continuous (realSlice s₀) := by
  refine continuous_pi fun j => ?_
  simp only [realSlice]
  fun_prop

/-- **Division on a polydisc.** Under the hypotheses of `eq_mul_cauchyQuotient_of_line` for every
`s` in `ball s₀ r` (holomorphy region, nonvanishing of `Q` on the circle, bound on the roots), and
if almost every real line `t ↦ s₀ + i(x + t v)` with `‖x‖ < r` carries a square-integrable `H/Q`
on `(-T, T)`, then `H = Q · cauchyQuotient H` on `ball s₀ r`. -/
theorem eqOn_mul_cauchyQuotient (S : Finset ι) (ℓ : ι → (Fin n → ℂ) →ₗ[ℂ] ℂ) (m : ℕ)
    (hreal : ∀ β ∈ S, ∀ x : Fin n → ℝ, (ℓ β (fun j => (x j : ℂ))).im = 0)
    (s₀ : Fin n → ℂ) (v : Fin n → ℝ) (hv : ∀ β ∈ S, realPart (ℓ β) v ≠ 0) {R T r : ℝ}
    (hR : 0 < R) (hTR : T ≤ 2 * R) (hr : 0 < r) {H : (Fin n → ℂ) → ℂ} {W : Set (Fin n → ℂ)}
    (hW : IsOpen W) (hH : DifferentiableOn ℂ H W)
    (h1 : ∀ s ∈ ball s₀ r, ∀ z ∈ ball (0 : ℂ) (2 * R), s + z • (Complex.I • ofRealVec v) ∈ W)
    (h2 : ∀ s ∈ ball s₀ r, ∀ z ∈ sphere (0 : ℂ) R,
      rootProduct S ℓ m s₀ (s + z • (Complex.I • ofRealVec v)) ≠ 0)
    (h3 : ∀ x : Fin n → ℝ, ‖x‖ < r → ∀ β ∈ S, |realPart (ℓ β) x / realPart (ℓ β) v| < T)
    (hgood : ∀ᵐ x : Fin n → ℝ, ‖x‖ < r → IntegrableOn (fun t : ℝ =>
      ‖H (realSlice s₀ (x + t • v)) / rootProduct S ℓ m s₀ (realSlice s₀ (x + t • v))‖ ^ 2)
      (Ioo (-T) T)) :
    ∀ s ∈ ball s₀ r, H s = rootProduct S ℓ m s₀ s *
      cauchyQuotient S ℓ m s₀ (Complex.I • ofRealVec v) R H s := by
  set u : Fin n → ℂ := Complex.I • ofRealVec v with hu
  have hsph : ∀ z ∈ sphere (0 : ℂ) R, z ∈ ball (0 : ℂ) (2 * R) := by
    intro z hz
    rw [mem_sphere_zero_iff_norm] at hz
    rw [mem_ball_zero_iff, hz]
    linarith
  have hballW : ball s₀ r ⊆ W := by
    intro s hs
    have := h1 s hs 0 (mem_ball_self (by linarith))
    simpa using this
  have hcq : DifferentiableOn ℂ (cauchyQuotient S ℓ m s₀ u R H) (ball s₀ r) :=
    differentiableOn_cauchyQuotient S ℓ m s₀ u hR hW hH isOpen_ball
      (fun s hs z hz => h1 s hs z (hsph z hz)) h2
  let G : (Fin n → ℂ) → ℂ := fun s => H s - rootProduct S ℓ m s₀ s * cauchyQuotient S ℓ m s₀ u R H s
  have hG : DifferentiableOn ℂ G (ball s₀ r) :=
    (hH.mono hballW).sub (((differentiable_rootProduct S ℓ m s₀).differentiableOn).mul hcq)
  have hmaps : ∀ x ∈ ball (0 : Fin n → ℝ) r, realSlice s₀ x ∈ ball s₀ r := by
    intro x hx
    rw [mem_ball, dist_realSlice]
    rwa [mem_ball, dist_zero_right] at hx
  have hslice : EqOn (fun x => G (realSlice s₀ x)) 0 (ball (0 : Fin n → ℝ) r) := by
    refine Measure.eqOn_open_of_ae_eq (μ := volume) ?_ isOpen_ball
      (hG.continuousOn.comp (continuous_realSlice s₀).continuousOn hmaps) continuousOn_const
    filter_upwards [ae_restrict_mem measurableSet_ball, ae_restrict_of_ae hgood] with x hx hxg
    rw [mem_ball, dist_zero_right] at hx
    have hxs : realSlice s₀ x ∈ ball s₀ r := by rw [mem_ball, dist_realSlice]; exact hx
    have := eq_mul_cauchyQuotient_of_line S ℓ m hreal s₀ v hv hR hTR hW hH x
      (h1 _ hxs) (h2 _ hxs) (h3 x hx) (hxg hx)
    simp only [G, Pi.zero_apply]
    rw [sub_eq_zero]
    exact this
  have hzero := eqOn_zero_of_realSlice hG hr fun x hx => by
    have := hslice (show x ∈ ball (0 : Fin n → ℝ) r by rwa [mem_ball, dist_zero_right])
    simpa using this
  intro s hs
  have := hzero hs
  simp only [G, Pi.zero_apply, sub_eq_zero] at this
  exact this

set_option maxHeartbeats 2000000 in
/-- **Convergence of Cauchy quotients.** If `H k → Hlim` locally uniformly on `W`, the circle
`{s + z u : |z| = R}` lies in `W` and `Q` does not vanish on it, then
`cauchyQuotient (H k) s → cauchyQuotient Hlim s`. -/
theorem tendsto_cauchyQuotient (S : Finset ι) (ℓ : ι → (Fin n → ℂ) →ₗ[ℂ] ℂ) (m : ℕ)
    (s₀ u : Fin n → ℂ) {R : ℝ} (hR : 0 < R) {W : Set (Fin n → ℂ)} (hW : IsOpen W)
    {s : Fin n → ℂ} (h1 : ∀ z ∈ sphere (0 : ℂ) R, s + z • u ∈ W)
    (h2 : ∀ z ∈ sphere (0 : ℂ) R, rootProduct S ℓ m s₀ (s + z • u) ≠ 0)
    {κ : Type*} {L : Filter κ} {H : κ → (Fin n → ℂ) → ℂ} {Hlim : (Fin n → ℂ) → ℂ}
    (hlim : TendstoLocallyUniformlyOn H Hlim L W) (hHlim : ContinuousOn Hlim W)
    (hH : ∀ᶠ k in L, ContinuousOn (H k) W) :
    Tendsto (fun k => cauchyQuotient S ℓ m s₀ u R (H k) s) L
      (𝓝 (cauchyQuotient S ℓ m s₀ u R Hlim s)) := by
  set Q := rootProduct S ℓ m s₀ with hQ
  let γ : ℂ → (Fin n → ℂ) := fun z => s + z • u
  have hγc : Continuous γ := by fun_prop
  have hker : ∀ {G : (Fin n → ℂ) → ℂ}, ContinuousOn G W →
      ContinuousOn (fun z => cauchyKernel S ℓ m s₀ u G s z) (sphere 0 R) := by
    intro G hG
    have := continuousOn_cauchyKernel S ℓ m s₀ u hR hG (K := {s})
      (fun s' hs' z hz => by rw [mem_singleton_iff.1 hs']; exact h1 z hz)
      (fun s' hs' z hz => by rw [mem_singleton_iff.1 hs']; exact h2 z hz)
    exact this.comp (continuous_const.prodMk continuous_id).continuousOn
      (fun z hz => ⟨mem_singleton s, hz⟩)
  have hKc : IsCompact (γ '' sphere (0 : ℂ) R) := (isCompact_sphere 0 R).image hγc
  have hKcW : γ '' sphere (0 : ℂ) R ⊆ W := by
    rintro _ ⟨z, hz, rfl⟩
    exact h1 z hz
  have hunif : TendstoUniformlyOn H Hlim L (γ '' sphere (0 : ℂ) R) :=
    (tendstoLocallyUniformlyOn_iff_forall_isCompact hW).1 hlim _ hKcW hKc
  have hQc : ContinuousOn (fun z => ‖Q (γ z)‖) (sphere (0 : ℂ) R) :=
    ((continuous_rootProduct S ℓ m s₀).comp hγc).norm.continuousOn
  obtain ⟨z₀, hz₀, hmin⟩ := (isCompact_sphere (0 : ℂ) R).exists_isMinOn
    (NormedSpace.sphere_nonempty.2 hR.le) hQc
  set q₀ := ‖Q (γ z₀)‖ with hq₀def
  have hq₀ : 0 < q₀ := norm_pos_iff.2 (h2 z₀ hz₀)
  rw [Metric.tendsto_nhds]
  intro ε hε
  have hev := Metric.tendstoUniformlyOn_iff.1 hunif (ε * q₀ / 2) (by positivity)
  filter_upwards [hev, hH] with k hk hHk
  have hdiff : cauchyQuotient S ℓ m s₀ u R (H k) s - cauchyQuotient S ℓ m s₀ u R Hlim s =
      (2 * π * Complex.I)⁻¹ * ∮ z in C(0, R),
        (cauchyKernel S ℓ m s₀ u (H k) s z - cauchyKernel S ℓ m s₀ u Hlim s z) := by
    rw [circleIntegral.integral_sub ((hker hHk).circleIntegrable hR.le)
      ((hker hHlim).circleIntegrable hR.le), mul_sub]
    rfl
  have hbound : ∀ z ∈ sphere (0 : ℂ) R,
      ‖cauchyKernel S ℓ m s₀ u (H k) s z - cauchyKernel S ℓ m s₀ u Hlim s z‖ ≤
        R⁻¹ * ((ε * q₀ / 2) * q₀⁻¹) := by
    intro z hz
    have hzR : ‖z‖ = R := mem_sphere_zero_iff_norm.1 hz
    have hd : dist (Hlim (γ z)) (H k (γ z)) < ε * q₀ / 2 := hk (γ z) ⟨z, hz, rfl⟩
    rw [dist_eq_norm, norm_sub_rev] at hd
    have hQ' : ‖Q (γ z)‖⁻¹ ≤ q₀⁻¹ := inv_anti₀ hq₀ (hmin hz)
    have heq : cauchyKernel S ℓ m s₀ u (H k) s z - cauchyKernel S ℓ m s₀ u Hlim s z =
        z⁻¹ * ((H k (γ z) - Hlim (γ z)) * (Q (γ z))⁻¹) := by
      simp only [cauchyKernel, γ, hQ]
      ring
    rw [heq, norm_mul, norm_mul, norm_inv, norm_inv, hzR]
    refine mul_le_mul_of_nonneg_left ?_ (inv_nonneg.2 hR.le)
    exact mul_le_mul hd.le hQ' (inv_nonneg.2 (norm_nonneg _)) (by positivity)
  have hint := circleIntegral.norm_integral_le_of_norm_le_const hR.le hbound
  have h2pi : ‖(2 * π * Complex.I)⁻¹‖ = (2 * π)⁻¹ := by
    rw [norm_inv, norm_mul, norm_mul, Complex.norm_I, mul_one, Complex.norm_real,
      Real.norm_eq_abs, abs_of_pos pi_pos, Complex.norm_ofNat]
  rw [dist_eq_norm, hdiff, norm_mul, h2pi]
  calc (2 * π)⁻¹ * ‖∮ z in C(0, R), (cauchyKernel S ℓ m s₀ u (H k) s z -
          cauchyKernel S ℓ m s₀ u Hlim s z)‖
      ≤ (2 * π)⁻¹ * (2 * π * R * (R⁻¹ * ((ε * q₀ / 2) * q₀⁻¹))) :=
        mul_le_mul_of_nonneg_left hint (by positivity)
    _ = ε / 2 := by
        field_simp
    _ < ε := by linarith

/-- The zero set of a nonzero linear form, translated to `s₀`, has empty interior. -/
theorem interior_setOf_linearMap_eq_zero {ℓ : (Fin n → ℂ) →ₗ[ℂ] ℂ} (hℓ : ℓ ≠ 0)
    (s₀ : Fin n → ℂ) : interior {s | ℓ (s - s₀) = 0} = ∅ := by
  by_contra h
  obtain ⟨p, hp⟩ := nonempty_iff_ne_empty.2 h
  obtain ⟨ε, hε, hball⟩ := Metric.isOpen_iff.1 isOpen_interior p hp
  apply hℓ
  refine LinearMap.ext fun z => ?_
  set t : ℝ := ε / (2 * (‖z‖ + 1)) with ht
  have htpos : 0 < t := by positivity
  have hmem : p + (t : ℂ) • z ∈ ball p ε := by
    rw [mem_ball, dist_eq_norm, add_sub_cancel_left, norm_smul, Complex.norm_real,
      Real.norm_eq_abs, abs_of_pos htpos]
    have h1 : t * ‖z‖ ≤ t * (‖z‖ + 1) := by nlinarith [norm_nonneg z]
    have h2 : t * (‖z‖ + 1) = ε / 2 := by rw [ht]; field_simp
    linarith
  have h1' : p + (t : ℂ) • z ∈ {s | ℓ (s - s₀) = 0} := interior_subset (hball hmem)
  have h2' : p ∈ {s | ℓ (s - s₀) = 0} := interior_subset hp
  have h1 : ℓ (p + (t : ℂ) • z - s₀) = 0 := h1'
  have h2 : ℓ (p - s₀) = 0 := h2'
  have h3 : ℓ (p + (t : ℂ) • z - s₀) = ℓ (p - s₀) + (t : ℂ) * ℓ z := by
    rw [add_sub_right_comm, map_add, map_smul, smul_eq_mul]
  rw [h1, h2, zero_add] at h3
  have htc : (t : ℂ) ≠ 0 := by exact_mod_cast htpos.ne'
  rw [LinearMap.zero_apply]
  exact (mul_eq_zero.1 h3.symm).resolve_left htc

theorem isOpen_setOf_rootProduct_ne_zero (S : Finset ι) (ℓ : ι → (Fin n → ℂ) →ₗ[ℂ] ℂ) (m : ℕ)
    (s₀ : Fin n → ℂ) : IsOpen {s | rootProduct S ℓ m s₀ s ≠ 0} :=
  isOpen_ne_fun (continuous_rootProduct S ℓ m s₀) continuous_const

/-- **Density of the regular set.** If every `ℓ β` (`β ∈ S`) is nonzero, the set where
`Q = ∏ β ∈ S, ℓ β (· - s₀) ^ m` does not vanish is dense. -/
theorem dense_setOf_rootProduct_ne_zero (S : Finset ι) (ℓ : ι → (Fin n → ℂ) →ₗ[ℂ] ℂ)
    (hℓ : ∀ β ∈ S, ℓ β ≠ 0) (m : ℕ) (s₀ : Fin n → ℂ) :
    Dense {s | rootProduct S ℓ m s₀ s ≠ 0} := by
  classical
  have hcompl : {s | rootProduct S ℓ m s₀ s ≠ 0} = {s | rootProduct S ℓ m s₀ s = 0}ᶜ := by
    ext s
    simp
  rw [hcompl, ← interior_eq_empty_iff_dense_compl]
  have hsub : {s | rootProduct S ℓ m s₀ s = 0} ⊆ ⋃ β ∈ S, {s | ℓ β (s - s₀) = 0} := by
    intro s hs
    simp only [mem_ofPred_eq, rootProduct, Finset.prod_eq_zero_iff] at hs
    obtain ⟨β, hβ, h0⟩ := hs
    exact mem_biUnion hβ (pow_eq_zero_iff'.1 h0).1
  have hint : ∀ T : Finset ι, T ⊆ S → interior (⋃ β ∈ T, {s | ℓ β (s - s₀) = 0}) = ∅ := by
    intro T
    induction T using Finset.induction_on with
    | empty => intro _; simp
    | insert β T hβ ih =>
      intro hTS
      rw [Finset.set_biUnion_insert]
      have hcl : IsClosed {s : Fin n → ℂ | ℓ β (s - s₀) = 0} :=
        isClosed_eq ((continuous_linearMap_apply (ℓ β)).comp (continuous_id.sub continuous_const))
          continuous_const
      rw [interior_union_isClosed_of_interior_empty hcl
        (ih ((Finset.subset_insert β T).trans hTS))]
      exact interior_setOf_linearMap_eq_zero (hℓ β (hTS (Finset.mem_insert_self β T))) s₀
  exact eq_empty_of_subset_empty ((interior_mono hsub).trans (hint S subset_rfl).subset)

/-- The zero set of `Q` on the real slice is contained in finitely many proper real hyperplanes,
hence is a null set. -/
theorem volume_setOf_rootProduct_realSlice_eq_zero (S : Finset ι)
    (ℓ : ι → (Fin n → ℂ) →ₗ[ℂ] ℂ) (m : ℕ)
    (hreal : ∀ β ∈ S, ∀ x : Fin n → ℝ, (ℓ β (fun j => (x j : ℂ))).im = 0)
    (s₀ : Fin n → ℂ) (v : Fin n → ℝ) (hv : ∀ β ∈ S, realPart (ℓ β) v ≠ 0) :
    volume {x : Fin n → ℝ | rootProduct S ℓ m s₀ (realSlice s₀ x) = 0} = 0 := by
  have hsub : {x : Fin n → ℝ | rootProduct S ℓ m s₀ (realSlice s₀ x) = 0} ⊆
      ⋃ β ∈ (S : Set ι), (LinearMap.ker (realPart (ℓ β)) : Set (Fin n → ℝ)) := by
    intro x hx
    simp only [mem_ofPred_eq, rootProduct, Finset.prod_eq_zero_iff] at hx
    obtain ⟨β, hβ, h0⟩ := hx
    have h1 := (pow_eq_zero_iff'.1 h0).1
    rw [realSlice_sub, map_smul, smul_eq_mul, eq_realPart (hreal β hβ)] at h1
    have h2 : realPart (ℓ β) x = 0 := by
      have := (mul_eq_zero.1 h1).resolve_left Complex.I_ne_zero
      exact_mod_cast this
    exact mem_biUnion (Finset.mem_coe.2 hβ) h2
  refine measure_mono_null hsub ((measure_biUnion_null_iff S.countable_toSet).2 fun β hβ => ?_)
  refine Measure.addHaar_submodule volume _ fun htop => hv β hβ ?_
  have : v ∈ LinearMap.ker (realPart (ℓ β)) := by rw [htop]; trivial
  exact this

/-- **Division by a product of real linear forms, uniformly in a limit.** Let
`Q s = ∏ β ∈ S, ℓ β (s - s₀) ^ m` with every `ℓ β` nonzero and real on `ℝⁿ`, `W` open and
`s₀ + i x ∈ W` for `x ∈ ball 0 ρ`. There is one open `W' ∋ s₀`, `W' ⊆ W`, such that: whenever
`H k → Hlim` locally uniformly on `W` along a nontrivial filter, with `Hlim` and eventually every
`H k` holomorphic on `W`, and eventually the integrals of `|H k / Q|²` over the compact subsets of
the real ball `ball 0 ρ` (slice `s₀ + i x`) avoiding the zeros of `Q` are bounded, then
`Hlim = Q · H'` on `W'` with `H'` holomorphic on `W'`. -/
theorem exists_open_forall_tendsto_eq_rootProduct_mul (S : Finset ι)
    (ℓ : ι → (Fin n → ℂ) →ₗ[ℂ] ℂ) (hℓ : ∀ β ∈ S, ℓ β ≠ 0)
    (hreal : ∀ β ∈ S, ∀ x : Fin n → ℝ, (ℓ β (fun j => (x j : ℂ))).im = 0) (m : ℕ)
    (s₀ : Fin n → ℂ) {W : Set (Fin n → ℂ)} (hW : IsOpen W) {ρ : ℝ} (hρ : 0 < ρ)
    (hρW : ∀ x ∈ ball (0 : Fin n → ℝ) ρ, realSlice s₀ x ∈ W) :
    ∃ W' : Set (Fin n → ℂ), IsOpen W' ∧ s₀ ∈ W' ∧ W' ⊆ W ∧
      ∀ {κ : Type*} (L : Filter κ) [L.NeBot] (H : κ → (Fin n → ℂ) → ℂ)
        (Hlim : (Fin n → ℂ) → ℂ), DifferentiableOn ℂ Hlim W →
        (∀ᶠ k in L, DifferentiableOn ℂ (H k) W) → TendstoLocallyUniformlyOn H Hlim L W →
        (∀ᶠ k in L, ∃ C : ℝ, ∀ A : Set (Fin n → ℝ), IsCompact A → A ⊆ ball 0 ρ →
          (∀ x ∈ A, rootProduct S ℓ m s₀ (realSlice s₀ x) ≠ 0) →
          ∫ x in A, ‖H k (realSlice s₀ x) / rootProduct S ℓ m s₀ (realSlice s₀ x)‖ ^ 2 ≤ C) →
        ∃ H' : (Fin n → ℂ) → ℂ, DifferentiableOn ℂ H' W' ∧
          ∀ s ∈ W', Hlim s = rootProduct S ℓ m s₀ s * H' s := by
  have hs₀ : s₀ ∈ W := by
    have h := hρW 0 (mem_ball_self hρ)
    have h0 : realSlice s₀ 0 = s₀ := by
      ext j
      simp [realSlice]
    rwa [h0] at h
  rcases S.eq_empty_or_nonempty with hS | hSne
  · subst hS
    refine ⟨W, hW, hs₀, subset_rfl, fun L _ H Hlim hHlim _ _ _ => ⟨Hlim, hHlim, fun s _ => ?_⟩⟩
    simp [rootProduct]
  cases n with
  | zero =>
    exfalso
    obtain ⟨β, hβ⟩ := hSne
    apply hℓ β hβ
    refine LinearMap.ext fun z => ?_
    rw [Subsingleton.elim z 0, map_zero, LinearMap.zero_apply]
  | succ n =>
  obtain ⟨v, hv0, hv⟩ := exists_real_direction S ℓ hℓ hreal
  set u : Fin (n + 1) → ℂ := Complex.I • ofRealVec v with hu
  have hnu : ‖u‖ = ‖v‖ := by rw [hu, norm_smul, Complex.norm_I, one_mul, norm_ofRealVec]
  obtain ⟨R₀, hR₀, hR₀W⟩ : ∃ R₀ > 0, closedBall s₀ R₀ ⊆ W := by
    obtain ⟨ε, hε, hεW⟩ := Metric.isOpen_iff.1 hW s₀ hs₀
    exact ⟨ε / 2, by positivity, (closedBall_subset_ball (by linarith)).trans hεW⟩
  set Λ : ℝ := 1 + ∑ β ∈ S, ‖LinearMap.toContinuousLinearMap (ℓ β)‖ with hΛ
  have hΛpos : 0 < Λ := by positivity
  have hℓb : ∀ β ∈ S, ∀ z, ‖ℓ β z‖ ≤ Λ * ‖z‖ := by
    intro β hβ z
    have h1 : ‖ℓ β z‖ ≤ ‖LinearMap.toContinuousLinearMap (ℓ β)‖ * ‖z‖ := by
      simpa using (LinearMap.toContinuousLinearMap (ℓ β)).le_opNorm z
    have h2 : ‖LinearMap.toContinuousLinearMap (ℓ β)‖ ≤ Λ := by
      have := Finset.single_le_sum (f := fun β => ‖LinearMap.toContinuousLinearMap (ℓ β)‖)
        (fun _ _ => norm_nonneg _) hβ
      linarith
    exact h1.trans (mul_le_mul_of_nonneg_right h2 (norm_nonneg z))
  obtain ⟨β₀, hβ₀, hmin⟩ := S.exists_min_image (fun β => |realPart (ℓ β) v|) hSne
  set b₀ := |realPart (ℓ β₀) v| with hb₀
  have hb₀pos : 0 < b₀ := abs_pos.2 (hv β₀ hβ₀)
  set R := R₀ / (4 * (‖v‖ + 1)) with hR
  have hRpos : 0 < R := by positivity
  set T := min R (ρ / (4 * (1 + ‖v‖))) with hT
  have hTpos : 0 < T := lt_min hRpos (by positivity)
  have hTR : T ≤ R := min_le_left _ _
  have hTρ : 4 * T * (1 + ‖v‖) ≤ ρ := by
    have h1 : T ≤ ρ / (4 * (1 + ‖v‖)) := min_le_right _ _
    have h4 : 0 < 4 * (1 + ‖v‖) := by positivity
    calc 4 * T * (1 + ‖v‖) = T * (4 * (1 + ‖v‖)) := by ring
      _ ≤ ρ / (4 * (1 + ‖v‖)) * (4 * (1 + ‖v‖)) := by gcongr
      _ = ρ := by field_simp
  set r₁ := min T (ρ / (2 * (1 + ‖v‖))) with hr₁
  set r := min (min (R₀ / 4) r₁) (T * b₀ / (2 * Λ)) with hr
  have hrpos : 0 < r :=
    lt_min (lt_min (by positivity) (lt_min hTpos (by positivity))) (by positivity)
  have hrR₀ : r ≤ R₀ / 4 := (min_le_left _ _).trans (min_le_left _ _)
  have hrr₁ : r ≤ r₁ := (min_le_left _ _).trans (min_le_right _ _)
  have hΛr : Λ * r ≤ T * b₀ / 2 := by
    calc Λ * r ≤ Λ * (T * b₀ / (2 * Λ)) := by gcongr; exact min_le_right _ _
      _ = T * b₀ / 2 := by field_simp
  have hRv : 2 * R * ‖v‖ ≤ R₀ / 2 := by
    have h1 : R * (4 * (‖v‖ + 1)) = R₀ := by rw [hR]; field_simp
    nlinarith [hRpos, norm_nonneg v]
  -- the geometric hypotheses of `eqOn_mul_cauchyQuotient`
  have g1 : ∀ s ∈ ball s₀ r, ∀ z ∈ ball (0 : ℂ) (2 * R), s + z • u ∈ W := by
    intro s hs z hz
    apply hR₀W
    rw [mem_closedBall, dist_eq_norm]
    rw [mem_ball, dist_eq_norm] at hs
    rw [mem_ball, dist_zero_right] at hz
    have h1 : ‖s + z • u - s₀‖ ≤ ‖s - s₀‖ + ‖z‖ * ‖v‖ := by
      rw [add_sub_right_comm]
      calc ‖s - s₀ + z • u‖ ≤ ‖s - s₀‖ + ‖z • u‖ := norm_add_le _ _
        _ = ‖s - s₀‖ + ‖z‖ * ‖v‖ := by rw [norm_smul, hnu]
    have h2 : ‖z‖ * ‖v‖ ≤ 2 * R * ‖v‖ := mul_le_mul_of_nonneg_right hz.le (norm_nonneg v)
    linarith
  have hℓu : ∀ β ∈ S, ℓ β u = Complex.I * (realPart (ℓ β) v : ℂ) := by
    intro β hβ
    rw [hu, map_smul, smul_eq_mul, eq_realPart (hreal β hβ)]
  have g2 : ∀ s ∈ ball s₀ r, ∀ z ∈ sphere (0 : ℂ) R,
      rootProduct S ℓ m s₀ (s + z • u) ≠ 0 := by
    intro s hs z hz
    rw [mem_ball, dist_eq_norm] at hs
    rw [mem_sphere_zero_iff_norm] at hz
    unfold rootProduct
    rw [Finset.prod_ne_zero_iff]
    intro β hβ
    apply pow_ne_zero
    have hsplit : ℓ β (s + z • u - s₀) =
        ℓ β (s - s₀) + z * (Complex.I * (realPart (ℓ β) v : ℂ)) := by
      rw [add_sub_right_comm, map_add, map_smul, smul_eq_mul, hℓu β hβ]
    rw [hsplit]
    intro h0
    have hnorm : ‖z * (Complex.I * (realPart (ℓ β) v : ℂ))‖ = R * |realPart (ℓ β) v| := by
      rw [norm_mul, norm_mul, Complex.norm_I, one_mul, Complex.norm_real, Real.norm_eq_abs, hz]
    have heq : ‖z * (Complex.I * (realPart (ℓ β) v : ℂ))‖ = ‖ℓ β (s - s₀)‖ := by
      rw [eq_neg_of_add_eq_zero_right h0, norm_neg]
    have hle : ‖ℓ β (s - s₀)‖ < R * b₀ := by
      calc ‖ℓ β (s - s₀)‖ ≤ Λ * ‖s - s₀‖ := hℓb β hβ _
        _ ≤ Λ * r := by gcongr
        _ ≤ T * b₀ / 2 := hΛr
        _ < R * b₀ := by nlinarith
    have hge : R * b₀ ≤ R * |realPart (ℓ β) v| :=
      mul_le_mul_of_nonneg_left (hmin β hβ) hRpos.le
    linarith
  have g3 : ∀ x : Fin (n + 1) → ℝ, ‖x‖ < r → ∀ β ∈ S,
      |realPart (ℓ β) x / realPart (ℓ β) v| < T := by
    intro x hx β hβ
    have ha : |realPart (ℓ β) x| ≤ Λ * ‖x‖ := by
      rw [realPart_apply]
      calc |(ℓ β (ofRealVec x)).re| ≤ ‖ℓ β (ofRealVec x)‖ := Complex.abs_re_le_norm _
        _ ≤ Λ * ‖ofRealVec x‖ := hℓb β hβ _
        _ = Λ * ‖x‖ := by rw [norm_ofRealVec]
    have hb : b₀ ≤ |realPart (ℓ β) v| := hmin β hβ
    have hbpos : 0 < |realPart (ℓ β) v| := lt_of_lt_of_le hb₀pos hb
    rw [abs_div, div_lt_iff₀ hbpos]
    calc |realPart (ℓ β) x| ≤ Λ * ‖x‖ := ha
      _ ≤ Λ * r := by gcongr
      _ ≤ T * b₀ / 2 := hΛr
      _ < T * b₀ := by nlinarith
      _ ≤ T * |realPart (ℓ β) v| := mul_le_mul_of_nonneg_left hb hTpos.le
  have hW'W : ball s₀ r ⊆ W := fun s hs => by
    have h := g1 s hs 0 (mem_ball_self (by positivity))
    simpa using h
  refine ⟨ball s₀ r, isOpen_ball, mem_ball_self hrpos, hW'W, ?_⟩
  intro κ L _ H Hlim hHlim hH hlim hL2
  have hsph : ∀ z ∈ sphere (0 : ℂ) R, z ∈ ball (0 : ℂ) (2 * R) := by
    intro z hz
    rw [mem_sphere_zero_iff_norm] at hz
    rw [mem_ball_zero_iff, hz]
    linarith
  have hTR2 : T ≤ 2 * R := by linarith
  -- each `H k` is divisible by `Q` on `ball s₀ r`
  have hdiv : ∀ᶠ k in L, ∀ s ∈ ball s₀ r,
      H k s = rootProduct S ℓ m s₀ s * cauchyQuotient S ℓ m s₀ u R (H k) s := by
    filter_upwards [hH, hL2] with k hHk hCk
    obtain ⟨C, hC⟩ := hCk
    have hQc : Continuous fun x => rootProduct S ℓ m s₀ (realSlice s₀ x) :=
      (continuous_rootProduct S ℓ m s₀).comp (continuous_realSlice s₀)
    have hZc : IsClosed {x : Fin (n + 1) → ℝ | rootProduct S ℓ m s₀ (realSlice s₀ x) = 0} :=
      isClosed_eq hQc continuous_const
    have hZ0 := volume_setOf_rootProduct_realSlice_eq_zero S ℓ m hreal s₀ v hv
    have hfc : ContinuousOn (fun x => ‖H k (realSlice s₀ x) /
        rootProduct S ℓ m s₀ (realSlice s₀ x)‖ ^ 2)
        (ball 0 ρ \ {x | rootProduct S ℓ m s₀ (realSlice s₀ x) = 0}) := by
      have h1 : ContinuousOn (fun x => H k (realSlice s₀ x)) (ball 0 ρ) :=
        hHk.continuousOn.comp (continuous_realSlice s₀).continuousOn hρW
      have h2 := (h1.mono sdiff_subset).div hQc.continuousOn (fun x hx => hx.2)
      exact h2.norm.pow 2
    have hfint := integrableOn_of_forall_isCompact_le isOpen_ball isBounded_ball hZc hZ0 hfc
      (fun x => by positivity) (fun A hA hAU hAZ => hC A hA hAU hAZ)
    have hline := exists_ae_integrableOn_line v hv0 hfint hTpos hTρ
    have hgood : ∀ᵐ x : Fin (n + 1) → ℝ, ‖x‖ < r → IntegrableOn (fun t : ℝ =>
        ‖H k (realSlice s₀ (x + t • v)) / rootProduct S ℓ m s₀ (realSlice s₀ (x + t • v))‖ ^ 2)
        (Ioo (-T) T) :=
      hline.mono fun x hx hxr => hx (lt_of_lt_of_le hxr hrr₁)
    exact eqOn_mul_cauchyQuotient S ℓ m hreal s₀ v hv hRpos hTR2 hrpos hW hHk g1 g2 g3 hgood
  have hcq : DifferentiableOn ℂ (cauchyQuotient S ℓ m s₀ u R Hlim) (ball s₀ r) :=
    differentiableOn_cauchyQuotient S ℓ m s₀ u hRpos hW hHlim isOpen_ball
      (fun s hs z hz => g1 s hs z (hsph z hz)) g2
  refine ⟨cauchyQuotient S ℓ m s₀ u R Hlim, hcq, fun s hs => ?_⟩
  have ha : Tendsto (fun k => H k s) L (𝓝 (Hlim s)) := hlim.tendsto_at (hW'W hs)
  have hb := (tendsto_cauchyQuotient S ℓ m s₀ u hRpos hW (fun z hz => g1 s hs z (hsph z hz))
    (g2 s hs) hlim hHlim.continuousOn (hH.mono fun k hk => hk.continuousOn)).const_mul
    (rootProduct S ℓ m s₀ s)
  have ha' : Tendsto (fun k => H k s) L
      (𝓝 (rootProduct S ℓ m s₀ s * cauchyQuotient S ℓ m s₀ u R Hlim s)) :=
    hb.congr' (hdiv.mono fun k hk => (hk s hs).symm)
  exact tendsto_nhds_unique ha ha'

/-- **Division by a product of real linear forms, uniformly in a limit** (statement form of
`exists_open_forall_tendsto_eq_rootProduct_mul`, with the index types in universe `0`). -/
def RealHyperplaneDivisionStatement : Prop :=
  ∀ (n : ℕ) (ι : Type) (S : Finset ι) (ℓ : ι → (Fin n → ℂ) →ₗ[ℂ] ℂ), (∀ β ∈ S, ℓ β ≠ 0) →
    (∀ β ∈ S, ∀ x : Fin n → ℝ, (ℓ β (fun j => (x j : ℂ))).im = 0) → ∀ (m : ℕ)
    (s₀ : Fin n → ℂ) (W : Set (Fin n → ℂ)), IsOpen W → ∀ ρ : ℝ, 0 < ρ →
    (∀ x ∈ ball (0 : Fin n → ℝ) ρ, realSlice s₀ x ∈ W) →
    ∃ W' : Set (Fin n → ℂ), IsOpen W' ∧ s₀ ∈ W' ∧ W' ⊆ W ∧
      ∀ (κ : Type) (L : Filter κ), L.NeBot → ∀ (H : κ → (Fin n → ℂ) → ℂ)
        (Hlim : (Fin n → ℂ) → ℂ), DifferentiableOn ℂ Hlim W →
        (∀ᶠ k in L, DifferentiableOn ℂ (H k) W) → TendstoLocallyUniformlyOn H Hlim L W →
        (∀ᶠ k in L, ∃ C : ℝ, ∀ A : Set (Fin n → ℝ), IsCompact A → A ⊆ ball 0 ρ →
          (∀ x ∈ A, rootProduct S ℓ m s₀ (realSlice s₀ x) ≠ 0) →
          ∫ x in A, ‖H k (realSlice s₀ x) / rootProduct S ℓ m s₀ (realSlice s₀ x)‖ ^ 2 ≤ C) →
        ∃ H' : (Fin n → ℂ) → ℂ, DifferentiableOn ℂ H' W' ∧
          ∀ s ∈ W', Hlim s = rootProduct S ℓ m s₀ s * H' s

theorem realHyperplaneDivision : RealHyperplaneDivisionStatement := by
  intro n ι S ℓ hℓ hreal m s₀ W hW ρ hρ hρW
  obtain ⟨W', hW'o, hs₀, hW'W, h⟩ :=
    exists_open_forall_tendsto_eq_rootProduct_mul S ℓ hℓ hreal m s₀ hW hρ hρW
  exact ⟨W', hW'o, hs₀, hW'W, fun κ L hL H Hlim => @h κ L hL H Hlim⟩

end Langlands.Analysis.SeveralComplex
