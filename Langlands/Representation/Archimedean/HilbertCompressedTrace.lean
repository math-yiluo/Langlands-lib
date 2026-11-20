import Langlands.Representation.Archimedean.CompactKernelConvolution
import Langlands.Analysis.OperatorTraceFiniteCompression

/-! # Finite-dimensional Hilbert trace profiles and their kernel integrals -/

noncomputable section

open MeasureTheory Set Topology
open scoped Manifold ContDiff ComplexConjugate InnerProductSpace BigOperators

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

namespace Langlands.Archimedean

open Langlands.Analysis.OperatorIdeals
open DerivativeSmoothVectors (smoothedOperator)

section Group

variable {G : Type*} [Group G] {H P : Type*}
  [NormedAddCommGroup H] [InnerProductSpace ℂ H]
  [NormedAddCommGroup P] [InnerProductSpace ℂ P] [CompleteSpace P]
  (R : G →* (H →L[ℂ] H)) (i : P →L[ℂ] H) (p : H →L[ℂ] P)

/-- The finite-dimensional trace profile of the group action with the specified insertion
and projection. -/
def hilbertCompressionTrace [FiniteDimensional ℂ P] (g : G) : ℂ :=
  operatorTrace ((p.comp (R g)).comp i)

variable [FiniteDimensional ℂ P]

/-- A choice of finite orthonormal basis expresses the profile as a finite sum of usual
bounded matrix coefficients. -/
theorem hilbertCompressionTrace_eq_sum (g : G) {ι : Type*} [Fintype ι]
    (b : OrthonormalBasis ι ℂ P) :
    hilbertCompressionTrace R i p g = ∑ k, ⟪b k, p (R g (i (b k)))⟫_ℂ :=
  operatorTrace_eq_sum_diagonal b _

variable [TopologicalSpace G]

/-- The compressed trace is continuous for a jointly continuous action. -/
theorem continuous_hilbertCompressionTrace (hR : IsContinuousRepresentation R) :
    Continuous (hilbertCompressionTrace R i p) := by
  let b := stdOrthonormalBasis ℂ P
  simp_rw [show hilbertCompressionTrace R i p = fun g => ∑ k, ⟪b k, p (R g (i (b k)))⟫_ℂ
    from funext fun g => hilbertCompressionTrace_eq_sum R i p g b]
  apply continuous_finsetSum _ fun k _ => ?_
  exact ((innerSL ℂ (b k)).continuous.comp p.continuous).comp
    (hR.comp (continuous_id.prodMk continuous_const))

end Group

section Units

variable {A : Type*} [NormedRing A] [NormedAlgebra ℝ A] [CompleteSpace A]
  [MeasurableSpace Aˣ] [BorelSpace Aˣ] (μ : Measure Aˣ) [IsFiniteMeasureOnCompacts μ]
  {H P : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
  [NormedAddCommGroup P] [InnerProductSpace ℂ P] [CompleteSpace P] [FiniteDimensional ℂ P]
  (R : Aˣ →* (H →L[ℂ] H)) (i : P →L[ℂ] H) (p : H →L[ℂ] P)

local notation "I" => 𝓘(ℝ, A)

omit [NormedAlgebra ℝ A] [CompleteSpace A] in
private theorem integrable_inverseKernel_smul {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
    {κ : Aˣ → ℂ} (hκ : Continuous κ) (hkc : HasCompactSupport κ)
    {f : Aˣ → E} (hf : Continuous f) : Integrable (fun g => κ g⁻¹ • f g) μ :=
  ((hκ.comp continuous_inv).smul hf).integrable_of_hasCompactSupport
    ((hkc.comp_homeomorph (Homeomorph.inv Aˣ)).smul_right)

omit [NormedAlgebra ℝ A] [CompleteSpace A] in
/-- The trace obtained by composing a bounded kernel average with a finite-dimensional
compression equals the scalar kernel integral of its continuous trace profile. -/
theorem operatorTrace_smoothedOperator_comp_finite (hR : IsContinuousRepresentation R)
    {κ : Aˣ → ℂ} (hκ : Continuous κ) (hkc : HasCompactSupport κ) :
    operatorTrace ((smoothedOperator R μ hR κ hκ hkc).comp (i.comp p)) =
      ∫ g, κ g⁻¹ * hilbertCompressionTrace R i p g ∂μ := by
  let T := smoothedOperator R μ hR κ hκ hkc
  let b := stdOrthonormalBasis ℂ P
  have hc := (operatorTrace_finite_compression (T.comp i) p).2
  rw [ContinuousLinearMap.comp_assoc] at hc
  change operatorTrace (T.comp (i.comp p)) = _
  rw [hc, operatorTrace_eq_sum_diagonal b]
  simp_rw [hilbertCompressionTrace_eq_sum R i p _ b, Finset.mul_sum]
  have hC (k : Fin (Module.finrank ℂ P)) : Continuous (fun g : Aˣ => ⟪b k, p (R g (i (b k)))⟫_ℂ) :=
    ((innerSL ℂ (b k)).continuous.comp p.continuous).comp
      (hR.comp (continuous_id.prodMk continuous_const))
  have hI (k : Fin (Module.finrank ℂ P)) :
      Integrable (fun g : Aˣ => κ g⁻¹ * ⟪b k, p (R g (i (b k)))⟫_ℂ) μ := by
    simpa only [smul_eq_mul] using integrable_inverseKernel_smul μ hκ hkc (hC k)
  rw [integral_finsetSum Finset.univ fun k _ => hI k]
  refine Finset.sum_congr rfl fun k _ => ?_
  let L := (innerSL ℂ (b k)).comp p
  have hi : Integrable (fun g => κ g⁻¹ • R g (i (b k))) μ :=
    integrable_inverseKernel_smul μ hκ hkc (hR.comp (continuous_id.prodMk continuous_const))
  change L (∫ g, κ g⁻¹ • R g (i (b k)) ∂μ) = _
  rw [← L.integral_comp_comm hi]
  apply integral_congr_ae
  exact Filter.Eventually.of_forall fun g => L.map_smul _ _

end Units

section Separation

variable {A : Type*} [NormedRing A] [NormedAlgebra ℝ A] [CompleteSpace A]
  [FiniteDimensional ℝ A] [MeasurableSpace Aˣ] [BorelSpace Aˣ]
  (μ : Measure Aˣ) [IsFiniteMeasureOnCompacts μ] [μ.IsOpenPosMeasure]

local notation "I" => 𝓘(ℝ, A)

/-- Smooth compact inverse kernels distinguish continuous scalar functions pointwise. -/
theorem continuous_eq_of_inverseKernel_integral_eq {f g : Aˣ → ℂ}
    (hf : Continuous f) (hg : Continuous g)
    (h : ∀ κ : Aˣ → ℂ, ContMDiff I 𝓘(ℝ, ℂ) ∞ κ → HasCompactSupport κ →
      (∫ x, κ x⁻¹ * f x ∂μ) = ∫ x, κ x⁻¹ * g x ∂μ) : f = g := by
  let : LocallyCompactSpace Aˣ := Units.isOpenEmbedding_val.locallyCompactSpace
  funext x
  by_contra hn
  let d := fun y => f y - g y
  let z := conj (d x)
  let q := fun y => (z * d y).re
  have hd : Continuous d := hf.sub hg
  have hq : Continuous q := Complex.continuous_re.comp (continuous_const.mul hd)
  have hx : 0 < q x := by
    have hne : d x ≠ 0 := sub_ne_zero.mpr hn
    change 0 < (conj (d x) * d x).re
    rw [← Complex.normSq_eq_conj_mul_self, Complex.ofReal_re]
    exact Complex.normSq_pos.mpr hne
  let U : Set Aˣ := {y | 0 < q y⁻¹}
  have hqInv : Continuous (fun y : Aˣ => q y⁻¹) := hq.comp continuous_inv
  have hxInv : 0 < q (x⁻¹)⁻¹ := by simpa only [inv_inv] using hx
  have hU : U ∈ 𝓝 x⁻¹ := hqInv.continuousAt (lt_mem_nhds hxInv)
  obtain ⟨b, -, hbU⟩ :=
    (SmoothBumpFunction.nhds_basis_tsupport («I» := I) x⁻¹).mem_iff.mp hU
  let κ := fun y : Aˣ => (b y : ℂ)
  have hκ : ContMDiff I 𝓘(ℝ, ℂ) ∞ κ := Complex.ofRealCLM.contDiff.contMDiff.comp b.contMDiff
  have hκc : HasCompactSupport κ := b.hasCompactSupport.comp_left Complex.ofReal_zero
  have hI (r : Aˣ → ℂ) (hr : Continuous r) : Integrable (fun y => κ y⁻¹ * r y) μ := by
    simpa only [smul_eq_mul] using integrable_inverseKernel_smul μ hκ.continuous hκc hr
  have hz : (∫ y, κ y⁻¹ * d y ∂μ) = 0 := by
    simp only [d, mul_sub]
    rw [integral_sub (hI f hf) (hI g hg), h κ hκ hκc, sub_self]
  let t := fun y : Aˣ => b y⁻¹ * q y
  have ht : Continuous t := (b.continuous.comp continuous_inv).mul hq
  have htc : HasCompactSupport t := (b.hasCompactSupport.comp_homeomorph (Homeomorph.inv Aˣ)).mul_right
  have htn (y : Aˣ) : 0 ≤ t y := by
    by_cases hy : b y⁻¹ = 0
    · simp [t, hy]
    · have hpos : 0 < q y := by
        have hu : y⁻¹ ∈ U := hbU (subset_tsupport b hy)
        change 0 < q (y⁻¹)⁻¹ at hu
        simpa only [inv_inv] using hu
      exact mul_nonneg b.nonneg hpos.le
  have htx : 0 < t x := by simpa only [t, b.eq_one, one_mul] using hx
  have hpos : 0 < ∫ y, t y ∂μ :=
    ht.integral_pos_of_hasCompactSupport_nonneg_nonzero htc htn (x := x) htx.ne'
  have he : t = fun y => (z * (κ y⁻¹ * d y)).re := by
    funext y
    change b y⁻¹ * (z * d y).re = (z * ((b y⁻¹ : ℂ) * d y)).re
    rw [mul_left_comm, Complex.re_ofReal_mul]
  rw [he] at hpos
  change 0 < ∫ y, RCLike.re (z * (κ y⁻¹ * d y)) ∂μ at hpos
  rw [integral_re ((hI d hd).const_mul z), integral_const_mul, hz, mul_zero, RCLike.zero_re] at hpos
  exact (lt_irrefl _) hpos

variable [μ.IsMulRightInvariant]
  {X : Type*} [TopologicalSpace X] [CompactSpace X] [T2Space X] [MeasurableSpace X] [BorelSpace X]
  (ν : Measure X) [IsFiniteMeasure ν] (j : C(X, Aˣ)) (w : C(X, ℂ))
  {H J P Q : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
  [NormedAddCommGroup J] [InnerProductSpace ℂ J] [CompleteSpace J]
  [NormedAddCommGroup P] [InnerProductSpace ℂ P] [CompleteSpace P] [FiniteDimensional ℂ P]
  [NormedAddCommGroup Q] [InnerProductSpace ℂ Q] [CompleteSpace Q] [FiniteDimensional ℂ Q]
  (R : Aˣ →* (H →L[ℂ] H)) (S : Aˣ →* (J →L[ℂ] J))
  (i : P →L[ℂ] H) (p : H →L[ℂ] P) (k : Q →L[ℂ] J) (q : J →L[ℂ] Q)

/-- Equality of all smooth compact kernel traces implies equality of finite trace profiles
when the compression maps factor the same compact orbit average in each representation. -/
theorem hilbertCompressionTrace_eq_of_kernelTrace_eq
    (hR : IsContinuousRepresentation R) (hS : IsContinuousRepresentation S)
    (hPR : ∀ v : H, i (p v) = ∫ x, w x • R (j x) v ∂ν)
    (hPS : ∀ v : J, k (q v) = ∫ x, w x • S (j x) v ∂ν)
    (h : ∀ (κ : Aˣ → ℂ) (hκ : ContMDiff I 𝓘(ℝ, ℂ) ∞ κ) (hkc : HasCompactSupport κ),
      operatorTrace (smoothedOperator R μ hR κ hκ.continuous hkc) =
        operatorTrace (smoothedOperator S μ hS κ hκ.continuous hkc)) :
    hilbertCompressionTrace R i p = hilbertCompressionTrace S k q := by
  apply continuous_eq_of_inverseKernel_integral_eq μ
    (continuous_hilbertCompressionTrace R i p hR) (continuous_hilbertCompressionTrace S k q hS)
  intro κ hκ hkc
  let η := compactKernelConvolution ν j w κ
  have hη := contMDiff_compactKernelConvolution ν j w hκ
  have hηc := hasCompactSupport_compactKernelConvolution ν j w hkc
  have heR : smoothedOperator R μ hR η hη.continuous hηc =
      (smoothedOperator R μ hR κ hκ.continuous hkc).comp (i.comp p) := by
    ext v
    rw [smoothedOperator_compactKernelConvolution ν j w R μ hR hκ hkc, ← hPR]
    rfl
  have heS : smoothedOperator S μ hS η hη.continuous hηc =
      (smoothedOperator S μ hS κ hκ.continuous hkc).comp (k.comp q) := by
    ext v
    rw [smoothedOperator_compactKernelConvolution ν j w S μ hS hκ hkc, ← hPS]
    rfl
  have hηtrace := h η hη hηc
  rw [heR, heS, operatorTrace_smoothedOperator_comp_finite μ R i p hR hκ.continuous hkc,
    operatorTrace_smoothedOperator_comp_finite μ S k q hS hκ.continuous hkc] at hηtrace
  exact hηtrace

end Separation

end Langlands.Archimedean
