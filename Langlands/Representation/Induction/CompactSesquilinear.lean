import Langlands.Representation.Induction.CompactPairingDuality
import Langlands.Representation.Unitary.InvariantSesquilinear

/-! # Compact integration and positivity reflection for sesquilinear forms -/

noncomputable section

open MeasureTheory
open scoped NNReal ComplexConjugate

namespace Langlands.Induction

universe uG uV

variable {G : Type uG} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
  {V : Type uV} [AddCommGroup V] [Module ℂ V]
  (P : Subgroup G) (τ : Representation ℂ P V)

/-- A sesquilinear coefficient pairing of smooth induced functions is locally
constant, without a topology on the coefficient vector space. -/
theorem sesquilinearPairing_isLocallyConstant (b : V →ₗ⋆[ℂ] V →ₗ[ℂ] ℂ)
    (f h : SmoothFunctions P τ) :
    IsLocallyConstant (fun x => b (eval P τ f x) (eval P τ h x)) :=
  (eval_isLocallyConstant P τ f).comp₂ (eval_isLocallyConstant P τ h)
    (fun v w => b v w)

/-- Integrate a supplied sesquilinear pairing when its actual scalar
integrands are integrable. -/
def integralSesquilinear (b : V →ₗ⋆[ℂ] V →ₗ[ℂ] ℂ)
    (K : Subgroup G) [MeasurableSpace K] (μ : Measure K)
    (hint : ∀ f h : SmoothFunctions P τ,
      Integrable (fun k : K => b (eval P τ f k) (eval P τ h k)) μ) :
    SmoothFunctions P τ →ₗ⋆[ℂ] SmoothFunctions P τ →ₗ[ℂ] ℂ where
  toFun f :=
    { toFun := fun h => ∫ k : K, b (eval P τ f k) (eval P τ h k) ∂μ
      map_add' := by
        intro h j
        change (∫ k : K, b (eval P τ f k) (eval P τ h k + eval P τ j k) ∂μ) = _
        simp_rw [map_add]
        exact integral_add (hint f h) (hint f j)
      map_smul' := by
        intro c h
        change (∫ k : K, b (eval P τ f k) (c • eval P τ h k) ∂μ) = _
        simp_rw [map_smul]
        exact integral_smul c _ }
  map_add' := by
    intro f h
    ext j
    change (∫ k : K, b (eval P τ f k + eval P τ h k) (eval P τ j k) ∂μ) = _
    simp_rw [map_add, LinearMap.add_apply]
    exact integral_add (hint f j) (hint h j)
  map_smul' := by
    intro c f
    ext h
    change (∫ k : K, b (c • eval P τ f k) (eval P τ h k) ∂μ) = _
    simp_rw [map_smulₛₗ, LinearMap.smul_apply]
    exact integral_smul (conj c) _

@[simp]
theorem integralSesquilinear_apply (b : V →ₗ⋆[ℂ] V →ₗ[ℂ] ℂ)
    (K : Subgroup G) [MeasurableSpace K] (μ : Measure K)
    (hint : ∀ f h : SmoothFunctions P τ,
      Integrable (fun k : K => b (eval P τ f k) (eval P τ h k)) μ)
    (f h : SmoothFunctions P τ) :
    integralSesquilinear P τ b K μ hint f h =
      ∫ k : K, b (eval P τ f k) (eval P τ h k) ∂μ := rfl

/-- Compact integration preserves Hermitian symmetry. -/
theorem integralSesquilinear_hermitian (b : V →ₗ⋆[ℂ] V →ₗ[ℂ] ℂ)
    (hb : ∀ v w, b w v = conj (b v w))
    (K : Subgroup G) [MeasurableSpace K] (μ : Measure K)
    (hint : ∀ f h : SmoothFunctions P τ,
      Integrable (fun k : K => b (eval P τ f k) (eval P τ h k)) μ)
    (f h : SmoothFunctions P τ) :
    integralSesquilinear P τ b K μ hint h f =
      conj (integralSesquilinear P τ b K μ hint f h) := by
  change (∫ k : K, b (eval P τ h k) (eval P τ f k) ∂μ) =
    conj (∫ k : K, b (eval P τ f k) (eval P τ h k) ∂μ)
  rw [← integral_conj]
  exact integral_congr_ae (Filter.Eventually.of_forall fun k => hb _ _)

/-- Scalar diagonal right-translation invariance is invariance of the
integrated sesquilinear form. -/
theorem integralSesquilinear_invariant (b : V →ₗ⋆[ℂ] V →ₗ[ℂ] ℂ)
    (K : Subgroup G) [MeasurableSpace K] (μ : Measure K)
    (hint : ∀ f h : SmoothFunctions P τ,
      Integrable (fun k : K => b (eval P τ f k) (eval P τ h k)) μ)
    (hinv : ∀ (g : G) (f h : SmoothFunctions P τ),
      (∫ k : K, b (eval P τ f ((k : G) * g)) (eval P τ h ((k : G) * g)) ∂μ) =
        ∫ k : K, b (eval P τ f k) (eval P τ h k) ∂μ)
    (g : G) (f h : SmoothFunctions P τ) :
    integralSesquilinear P τ b K μ hint (smoothInduced P τ g f) (smoothInduced P τ g h) =
      integralSesquilinear P τ b K μ hint f h :=
  hinv g f h

/-- Full-modulus covariance of a coefficient form gives the same covariance
of every scalar pairing of induced sections. -/
theorem sesquilinearPairing_covariant (b : V →ₗ⋆[ℂ] V →ₗ[ℂ] ℂ)
    (δ : P → ℝ≥0)
    (hb : ∀ q v w, b (τ q v) (τ q w) = ((δ q : ℝ) : ℂ) * b v w)
    (f h : SmoothFunctions P τ) (q : P) (x : G) :
    b (eval P τ f ((q : G) * x)) (eval P τ h ((q : G) * x)) =
      ((δ q : ℝ) : ℂ) * b (eval P τ f x) (eval P τ h x) := by
  rw [show eval P τ f ((q : G) * x) = τ q (eval P τ f x) from f.1.2 q x,
    show eval P τ h ((q : G) * x) = τ q (eval P τ h x) from h.1.2 q x, hb]

section TestSections

variable [NonarchimedeanGroup G] [WeaklyLocallyCompactSpace G]

/-- A smooth coefficient vector is the value on an open subgroup of an
actual smooth section supported in its parabolic saturation. -/
theorem exists_diagonal_test (hτ : IsSmooth τ) (v : V) :
    ∃ (L : OpenSubgroup G) (f : SmoothFunctions P τ),
      (∀ l : L, eval P τ f l = v) ∧
      ∀ y : G, eval P τ f y ≠ 0 → ∃ (q : P) (l : L), y = (q : G) * (l : G) := by
  obtain ⟨H, hv⟩ := hτ v
  obtain ⟨L, hL, _hle, hfix⟩ := exists_compact_conj_fixed P τ v H hv 1 ⊤
  let f := (compactDoubleCosetSection P τ L hL 1 v hfix).val
  refine ⟨L, f, ?_, ?_⟩
  · intro l
    simpa only [one_mul] using compactDoubleCosetSection_apply_mul P τ L hL 1 v hfix l
  · intro y hy
    obtain ⟨q, l, heq⟩ :=
      compactDoubleCosetSection_mem_of_ne_zero P τ L hL 1 v hfix y hy
    exact ⟨q, l, by simpa only [mul_one] using heq⟩

/-- Integration of a nonzero coefficient form is nonzero when the form
has nonnegative real full-modulus covariance. -/
theorem integralSesquilinear_ne_zero (b : V →ₗ⋆[ℂ] V →ₗ[ℂ] ℂ)
    (hb : b ≠ 0) (hτ : IsSmooth τ) (δ : P → ℝ≥0)
    (hcov : ∀ q v w, b (τ q v) (τ q w) = ((δ q : ℝ) : ℂ) * b v w)
    (K : Subgroup G) [MeasurableSpace K] (μ : Measure K) [μ.IsOpenPosMeasure]
    (hint : ∀ f h : SmoothFunctions P τ,
      Integrable (fun k : K => b (eval P τ f k) (eval P τ h k)) μ) :
    integralSesquilinear P τ b K μ hint ≠ 0 := by
  obtain ⟨v, hv⟩ := InvariantSesquilinear.exists_diagonal_ne_zero b hb
  obtain ⟨L, f, hval, hsupp⟩ := exists_diagonal_test P τ hτ v
  let ψ : G → ℂ := fun y => b (eval P τ f y) (eval P τ f y)
  have hψcov (q : P) (x : G) :
      ψ ((q : G) * x) = ((δ q : ℝ) : ℂ) * ψ x :=
    sesquilinearPairing_covariant P τ b δ hcov f f q x
  have hne := integral_ne_zero_of_doubleCoset P δ K μ ψ hψcov 1
    (by simpa only [mul_one] using hint f f) L (b v v) hv
    (fun l => by simp only [ψ, one_mul, hval])
    (by
      intro y hy
      have hfy : eval P τ f y ≠ 0 := by
        intro hz
        apply hy
        simp [ψ, hz]
      obtain ⟨q, l, heq⟩ := hsupp y hfy
      exact ⟨q, l, by simpa only [mul_one] using heq⟩)
  intro hzero
  apply hne
  have h := congrArg (fun B : SmoothFunctions P τ →ₗ⋆[ℂ]
    SmoothFunctions P τ →ₗ[ℂ] ℂ => B f f) hzero
  simpa only [mul_one, integralSesquilinear_apply, LinearMap.zero_apply] using h

/-- Nonnegativity of every integrated diagonal reflects to the coefficient
form, tested by sections constant near the identity. -/
theorem diagonal_nonneg_of_integral (b : V →ₗ⋆[ℂ] V →ₗ[ℂ] ℂ)
    (hb : ∀ v w, b w v = conj (b v w)) (hτ : IsSmooth τ) (δ : P → ℝ≥0)
    (hcov : ∀ q v w, b (τ q v) (τ q w) = ((δ q : ℝ) : ℂ) * b v w)
    (K : Subgroup G) [MeasurableSpace K] (μ : Measure K) [μ.IsOpenPosMeasure]
    (hint : ∀ f h : SmoothFunctions P τ,
      Integrable (fun k : K => b (eval P τ f k) (eval P τ h k)) μ)
    (hnonneg : ∀ f, 0 ≤ (integralSesquilinear P τ b K μ hint f f).re)
    (v : V) : 0 ≤ (b v v).re := by
  by_contra! hneg
  have hv : b v v ≠ 0 := by
    intro hzero
    rw [hzero, Complex.zero_re] at hneg
    exact lt_irrefl 0 hneg
  obtain ⟨L, f, hval, hsupp⟩ := exists_diagonal_test P τ hτ v
  let ψ : G → ℂ := fun y => b (eval P τ f y) (eval P τ f y)
  have hψcov (q : P) (x : G) :
      ψ ((q : G) * x) = ((δ q : ℝ) : ℂ) * ψ x :=
    sesquilinearPairing_covariant P τ b δ hcov f f q x
  have hψsupp (y : G) (hy : ψ y ≠ 0) :
      ∃ (q : P) (l : L), y = (q : G) * 1 * (l : G) := by
    have hfy : eval P τ f y ≠ 0 := by
      intro hz
      apply hy
      simp [ψ, hz]
    obtain ⟨q, l, heq⟩ := hsupp y hfy
    exact ⟨q, l, by simpa only [mul_one] using heq⟩
  have hψval (l : L) : ψ (1 * (l : G)) = b v v := by
    simp only [ψ, one_mul, hval]
  have hne := integral_ne_zero_of_doubleCoset P δ K μ ψ hψcov 1
    (by simpa only [mul_one] using hint f f) L (b v v) hv hψval hψsupp
  have hpoint (k : K) : (ψ k).re ≤ 0 := by
    by_cases hz : ψ k = 0
    · simp only [hz, Complex.zero_re, le_refl]
    · obtain ⟨q, l, heq⟩ := hψsupp k hz
      rw [heq, mul_assoc, hψcov, hψval]
      simp only [Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im,
        zero_mul, sub_zero]
      exact mul_nonpos_of_nonneg_of_nonpos (δ q).2 hneg.le
  have hle : (integralSesquilinear P τ b K μ hint f f).re ≤ 0 := by
    change RCLike.re (∫ k : K, ψ k ∂μ) ≤ 0
    rw [← integral_re (show Integrable (fun k : K => ψ k) μ from hint f f)]
    exact integral_nonpos hpoint
  have hre : (integralSesquilinear P τ b K μ hint f f).re = 0 :=
    le_antisymm hle (hnonneg f)
  have hreal := Complex.conj_eq_iff_re.mp
    (integralSesquilinear_hermitian P τ b hb K μ hint f f).symm
  have hzero : integralSesquilinear P τ b K μ hint f f = 0 := by
    rw [← hreal, hre, Complex.ofReal_zero]
  apply hne
  simpa only [mul_one, integralSesquilinear_apply] using hzero

/-- If the integrated coefficient form is an actual positive definite form,
the coefficient form itself is positive definite. Invariance of the
coefficient form is not required for this analytic reflection step. -/
def positiveCore_of_integral (b : V →ₗ⋆[ℂ] V →ₗ[ℂ] ℂ)
    (hb : ∀ v w, b w v = conj (b v w)) (hτ : IsSmooth τ) (δ : P → ℝ≥0)
    (hcov : ∀ q v w, b (τ q v) (τ q w) = ((δ q : ℝ) : ℂ) * b v w)
    (K : Subgroup G) [MeasurableSpace K] (μ : Measure K) [μ.IsOpenPosMeasure]
    (hint : ∀ f h : SmoothFunctions P τ,
      Integrable (fun k : K => b (eval P τ f k) (eval P τ h k)) μ)
    (a : InvariantPositiveForm (smoothInduced P τ))
    (heq : ∀ f h, integralSesquilinear P τ b K μ hint f h = a.inner f h) :
    InnerProductSpace.Core ℂ V where
  inner v w := b v w
  conj_inner_symm v w := by rw [hb, Complex.conj_conj]
  re_inner_nonneg := diagonal_nonneg_of_integral P τ b hb hτ δ hcov K μ hint
    (fun f => by rw [heq]; exact a.re_inner_nonneg f)
  add_left v w z := by simp only [map_add, LinearMap.add_apply]
  smul_left v w c := by simp only [map_smulₛₗ, LinearMap.smul_apply, smul_eq_mul]
  definite v hv := by
    obtain ⟨L, f, hval, hsupp⟩ := exists_diagonal_test P τ hτ v
    have hdiag (k : K) : b (eval P τ f k) (eval P τ f k) = 0 := by
      by_cases hz : eval P τ f k = 0
      · simp [hz]
      · obtain ⟨q, l, heq⟩ := hsupp k hz
        rw [heq, sesquilinearPairing_covariant P τ b δ hcov f f q l,
          hval, hv, mul_zero]
    have hzero : a.inner f f = 0 := by
      rw [← heq]
      change (∫ k : K, b (eval P τ f k) (eval P τ f k) ∂μ) = 0
      simp only [hdiag, integral_zero]
    have hf := a.definite f hzero
    have hv' := hval (1 : L)
    rw [hf] at hv'
    exact hv'.symm

end TestSections

end Langlands.Induction
