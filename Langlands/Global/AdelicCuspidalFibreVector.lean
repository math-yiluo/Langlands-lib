import Langlands.Automorphic.GroupSchemeFullAEL2Hilbert
import Langlands.Global.AdelicNormOneKernelVector
import Langlands.Global.AdelicNormOnePartialConvolutionDecayStatement
import Langlands.Global.AdelicFiniteVolumeProof
import Langlands.Global.AdelicRepresentationHeightPropernessProof
import Langlands.Global.LeftCosetDiagonalSwap

/-! # Cuspidal kernel vectors for Levi fibre pairings -/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry MeasureTheory Filter Set
open scoped CategoryTheory.MonObj CompactlySupported Pointwise Topology

set_option autoImplicit false

namespace Langlands.Global

open Langlands.GroupScheme Langlands.Automorphic.GroupSchemeFunctions AdelicGroupPoints
  PositiveRealTorus RepresentationGrowth

variable {F : Type u} [Field F] [NumberField F] {H : GroupScheme (Spec (CommRingCat.of F))}
  [IsAffine H.X.left] [LocallyOfFiniteType H.X.hom]
  (hH : IsConnectedReductive H)
  (T : CommGroupScheme (Spec (CommRingCat.of F))) (i : T.toGrp ⟶ H)
  (hi : Function.Injective (characterRestrict i)) [(characterRestrict i).range.FiniteIndex]
  (I : Type u) [Fintype I] (e : T.toGrp ≅ splitTorus (Spec (CommRingCat.of F)) I)
  (hc : IsCentral i)
  [(Measure.haar : Measure (normOneSubgroup F H)).IsMulRightInvariant]

local notation "A" => AdelicGroupPoints F H
local notation "A₁" => normOneSubgroup F H
local notation "X₁" => NormOneRationalQuotient F H
local notation "Γ₁" => rationalNormOneSubgroup F H
local notation "μ₁" => normOneRationalQuotientHaarMeasure F H
local notation "Q" => PositiveRationalQuotient F H T i
local notation "V" => Lp ℂ 2 (positiveRationalQuotientHaarMeasure F H T i)
local notation "S" => fullAEL2CuspidalSubmodule F H parabolicDynamic hH T i hi I e hc
local notation "Pos" => intrinsicSubgroup F T
local notation "νP" => normalizedPositiveHaarMeasure F H T i hi I e hc
local notation "pp" => positivePointMap F H T i
local notation "πP" => positiveFactor F H T i hi I e

/-- The orthogonal projection into the cuspidal space of the kernel vector for evaluation at `y`. -/
def cuspidalNormOneKernelVector (K : C_c(A, ℂ)) (y : A) : S :=
  (S).orthogonalProjectionOnto (normOneKernelVector T i hi I e hc (rightTranslateCc K y))

/-- The projected kernel vector computes the partial convolution of a cuspidal class. -/
theorem inner_cuspidalNormOneKernelVector (K : C_c(A, ℂ)) (y : A) (v : S) :
    inner ℂ (cuspidalNormOneKernelVector hH T i hi I e hc K y) v =
      normOnePartialConvolution T i K (v.val : Q → ℂ) y := by
  rw [cuspidalNormOneKernelVector, Submodule.inner_orthogonalProjectionOnto_eq_of_mem_right,
    normOnePartialConvolution_eq_inner T i hi I e hc]

/-- The projected kernel vectors are left invariant under rational points. -/
theorem cuspidalNormOneKernelVector_rational_mul (K : C_c(A, ℂ))
    (r : RationalGroupPoints F H) (y : A) :
    cuspidalNormOneKernelVector hH T i hi I e hc K (rational F H r * y) =
      cuspidalNormOneKernelVector hH T i hi I e hc K y := by
  apply ext_inner_right ℂ
  intro v
  simp only [inner_cuspidalNormOneKernelVector, normOnePartialConvolution_rational_mul]

/-- The positive coordinates of all nonzero projected kernel vectors lie in the image of the
kernel's support. -/
theorem cuspidalNormOneKernelVector_eq_zero_of_notMem (K : C_c(A, ℂ)) (y : A)
    (hy : πP y ∉ πP '' tsupport K) :
    cuspidalNormOneKernelVector hH T i hi I e hc K y = 0 := by
  apply ext_inner_right ℂ
  intro v
  rw [inner_zero_left, inner_cuspidalNormOneKernelVector]
  unfold normOnePartialConvolution
  have hz (n : A₁) : K ((n : A)⁻¹ * y) = 0 := by
    apply image_eq_zero_of_notMem_tsupport
    intro hn
    apply hy
    refine ⟨_, hn, ?_⟩
    rw [map_mul, map_inv, positiveFactor_normOne, inv_one, one_mul]
  simp [hz]

/-- With a continuous evaluation parameter and a jointly continuous family of kernels whose
supports are locally uniformly compact, the projected kernel vectors vary continuously. -/
theorem continuous_cuspidalNormOneKernelVector_comp {P : Type*} [TopologicalSpace P]
    (K : P → C_c(A, ℂ)) (y : P → A) (hy : Continuous y)
    (hK : Continuous fun x : P × A => K x.1 x.2)
    (hD : ∀ p₀ : P, ∃ U ∈ nhds p₀, ∃ D : Set A,
      IsCompact D ∧ ∀ p ∈ U, tsupport (K p) ⊆ D) :
    Continuous fun p => cuspidalNormOneKernelVector hH T i hi I e hc (K p) (y p) := by
  apply (S).orthogonalProjectionOnto.continuous.comp
    (continuous_normOneKernelVector_comp T i hi I e hc (fun p => rightTranslateCc (K p) (y p)) ?_ ?_)
  · exact hK.comp (continuous_fst.prodMk (continuous_snd.mul (hy.comp continuous_fst)))
  · intro p₀
    obtain ⟨U, hU, D, hDc, hDU⟩ := hD p₀
    obtain ⟨E, hEc, hE⟩ := exists_compact_mem_nhds (y p₀)
    refine ⟨U ∩ y ⁻¹' E, inter_mem hU (hy.continuousAt.preimage_mem_nhds hE),
      D * E⁻¹, hDc.mul hEc.inv, fun p hp => ?_⟩
    refine closure_minimal (fun z hz => ?_) (hDc.mul hEc.inv).isClosed
    have hz' : K p (z * y p) ≠ 0 := hz
    exact ⟨z * y p, hDU p hp.1 (subset_tsupport _ hz'), (y p)⁻¹,
      Set.inv_mem_inv.mpr hp.2, mul_inv_cancel_right _ _⟩

/-- Continuity of the cuspidal kernel vectors associated with a fixed kernel. -/
theorem continuous_cuspidalNormOneKernelVector (K : C_c(A, ℂ)) :
    Continuous (cuspidalNormOneKernelVector hH T i hi I e hc K) :=
  continuous_cuspidalNormOneKernelVector_comp hH T i hi I e hc (fun _ => K) id continuous_id
    (K.continuous.comp continuous_snd)
    (fun _ => ⟨univ, univ_mem, tsupport K, K.hasCompactSupport, fun _ _ => subset_rfl⟩)

section Bound

variable [IsAffineHom H.X.hom]

/-- Uniform rapid decay of the projected kernel vectors in the norm of the cuspidal space.
The representative can be chosen simultaneously for all positive coordinates in a compact set. -/
theorem exists_cuspidalNormOneKernelVector_weight_bound
    (hDecay : NormOnePartialConvolutionRapidDecayStatement.{u})
    {N : ℕ} (rho : MatrixRepresentation H (Fin N)) (hN : 0 < N) (hrho : IsClosedSubgroup rho)
    (K : C_c(A, ℂ)) (hK : IsAdelicTestFunction F H K) (B : Set A) (hB : IsCompact B) (m : ℕ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ x : A₁, ∃ r : RationalGroupPoints F H,
      ∀ b ∈ B, ‖cuspidalNormOneKernelVector hH T i hi I e hc K ((x : A) * b)‖ *
        adelicHeight F H rho (rational F H r * (x : A)) ^ m ≤ C := by
  obtain ⟨C, hC, hd⟩ := hDecay F H hH T i hi I e hc rho hN hrho K hK B hB m
  refine ⟨C, hC, fun x => ?_⟩
  obtain ⟨r, hr⟩ := hd x
  refine ⟨r, fun b hb => ?_⟩
  let v := cuspidalNormOneKernelVector hH T i hi I e hc K ((x : A) * b)
  have h := hr v.val v.property b hb
  change ‖normOnePartialConvolution T i K (v.val : Q → ℂ) (_ * (x : A) * b)‖ * _ ≤ C * ‖v‖ at h
  rw [mul_assoc, normOnePartialConvolution_rational_mul,
    ← inner_cuspidalNormOneKernelVector hH T i hi I e hc K ((x : A) * b) v] at h
  change ‖inner ℂ v v‖ * _ ≤ C * ‖v‖ at h
  rw [← inner_self_re_eq_norm (𝕜 := ℂ) v, inner_self_eq_norm_sq (𝕜 := ℂ) v] at h
  change ‖v‖ * _ ≤ C
  by_cases hv : v = 0
  · simpa [hv] using hC
  · apply le_of_mul_le_mul_right _ (norm_pos_iff.mpr hv)
    calc (‖v‖ * _) * ‖v‖ = ‖v‖ ^ 2 * adelicHeight F H rho (rational F H r * (x : A)) ^ m := by ring
      _ ≤ C * ‖v‖ := h

end Bound

section Integral

/-- The integrand defining the vector that represents a weighted pairing on a norm-one fibre. -/
def cuspidalFibreVectorIntegrand (K : C_c(A, ℂ)) (f : A → ℂ) (d : Pos → ℂ)
    (b : Pos) (p : Pos × X₁) : S := by
  let y : A := ↑(Quotient.out p.2 : A₁)
  exact (d p.1 * f (y * (pp b * pp p.1))) •
    cuspidalNormOneKernelVector hH T i hi I e hc K (y * pp p.1)

local notation "μf" => Measure.prod νP μ₁

/-- The vector representing a weighted fibre pairing is the integral of the projected kernel
vectors against the weighted fibre values. -/
def cuspidalFibreVector (K : C_c(A, ℂ)) (f : A → ℂ) (d : Pos → ℂ) (b : Pos) : S :=
  ∫ p : Pos × X₁, cuspidalFibreVectorIntegrand hH T i hi I e hc K f d b p ∂μf

/-- The fibre integrand is continuous on the product of positive points and the norm-one quotient. -/
theorem continuous_cuspidalFibreVectorIntegrand (K : C_c(A, ℂ)) (f : A → ℂ) (d : Pos → ℂ)
    (hf : Continuous f)
    (hfRat : ∀ (r : RationalGroupPoints F H) (a : A), f (rational F H r * a) = f a)
    (hd : Continuous d) (b : Pos) :
    Continuous (cuspidalFibreVectorIntegrand hH T i hi I e hc K f d b) := by
  let g : A₁ × Pos → S := fun p =>
    (d p.2 * f ((p.1 : A) * (pp b * pp p.2))) •
      cuspidalNormOneKernelVector hH T i hi I e hc K ((p.1 : A) * pp p.2)
  have hg : Continuous g := by
    have hpp : Continuous fun p : A₁ × Pos => pp p.2 := (pp).continuous.comp continuous_snd
    have hy : Continuous fun p : A₁ × Pos => (p.1 : A) := continuous_subtype_val.comp continuous_fst
    exact ((hd.comp continuous_snd).mul (hf.comp (hy.mul (continuous_const.mul hpp)))).smul
      ((continuous_cuspidalNormOneKernelVector hH T i hi I e hc K).comp (hy.mul hpp))
  have hdesc : Continuous fun p : X₁ × Pos => g (Quotient.out p.1, p.2) := by
    refine LeftCosetSpace.continuous_out_prod' Γ₁ g hg ?_
    rintro ⟨_, r, rfl⟩ x t
    have hr : ((rationalNormOne F H r : A₁) : A) = rational F H r := rfl
    simp only [g, Subgroup.coe_mul, hr, mul_assoc, hfRat, cuspidalNormOneKernelVector_rational_mul]
  change Continuous (fun p : Pos × X₁ => g (Quotient.out p.2, p.1))
  exact Continuous.comp' (g := fun p : X₁ × Pos => g (Quotient.out p.1, p.2))
    (f := (Prod.swap : Pos × X₁ → X₁ × Pos)) hdesc continuous_swap

/-- Its integral pairs with a cuspidal class by the conjugate of the corresponding partial
convolution. -/
theorem inner_cuspidalFibreVector (K : C_c(A, ℂ)) (f : A → ℂ) (d : Pos → ℂ)
    (b : Pos) (v : S)
    (hint : Integrable (cuspidalFibreVectorIntegrand hH T i hi I e hc K f d b) μf) :
    inner ℂ v (cuspidalFibreVector hH T i hi I e hc K f d b) =
      ∫ t, ∫ ξ : X₁,
        let y := ((Quotient.out ξ : A₁) : A)
        d t * f (y * (pp b * pp t)) *
          starRingEnd ℂ (normOnePartialConvolution T i K (v.val : Q → ℂ) (y * pp t)) ∂μ₁ ∂νP := by
  let := AdelicSiegelFactors.isFiniteMeasure_normOneRationalQuotientHaarMeasure_of_connectedReductive F H hH
  let := normalizedPositiveHaarMeasure_sigmaFinite F H T i hi I e hc
  rw [cuspidalFibreVector, ← integral_inner hint v, integral_prod _ (hint.const_inner v)]
  refine integral_congr_ae (Eventually.of_forall fun t => integral_congr_ae (Eventually.of_forall fun x => ?_))
  let y : A := (Quotient.out x : A₁)
  let s : ℂ := d t * f (y * (pp b * pp t))
  let w : S := cuspidalNormOneKernelVector hH T i hi I e hc K (y * pp t)
  change inner ℂ v (s • w) =
    s * starRingEnd ℂ (normOnePartialConvolution T i K (v.val : Q → ℂ) (y * pp t))
  calc
    inner ℂ v (s • w) = s * inner ℂ v w := inner_smul_right (𝕜 := ℂ) v w s
    _ = s * starRingEnd ℂ (inner ℂ w v) :=
      congrArg (s * ·) (inner_conj_symm (𝕜 := ℂ) v w).symm
    _ = _ := congrArg (fun z => s * starRingEnd ℂ z)
      (inner_cuspidalNormOneKernelVector hH T i hi I e hc K (y * pp t) v)

variable [IsAffineHom H.X.hom]

/-- Uniform rapid decay makes the fibre integrand integrable for any rationally invariant,
continuous input of polynomial growth. The integral is continuous in the positive parameter
and satisfies the same degree of polynomial growth in that parameter. -/
theorem cuspidalFibreVector_properties (hDecay : NormOnePartialConvolutionRapidDecayStatement.{u})
    {N : ℕ} (rho : MatrixRepresentation H (Fin N)) (hN : 0 < N) (hrho : IsClosedSubgroup rho)
    (K : C_c(A, ℂ)) (f : A → ℂ) (d : Pos → ℂ)
    (hK : IsAdelicTestFunction F H K) (hf : Continuous f)
    (hfRat : ∀ (r : RationalGroupPoints F H) (a : A), f (rational F H r * a) = f a)
    (hd : Continuous d) (m : ℕ) (M : ℝ) (hM : 0 ≤ M)
    (hfM : ∀ a, ‖f a‖ ≤ M * adelicHeight F H rho a ^ m) :
    (∀ b, Integrable (cuspidalFibreVectorIntegrand hH T i hi I e hc K f d b) μf) ∧
      Continuous (cuspidalFibreVector hH T i hi I e hc K f d) ∧
      ∃ C : ℝ, 0 ≤ C ∧ ∀ b,
        ‖cuspidalFibreVector hH T i hi I e hc K f d b‖ ≤ C * adelicHeight F H rho (pp b) ^ m := by
  let Fv := cuspidalFibreVectorIntegrand hH T i hi I e hc K f d
  let : T2Space Pos := (positiveLogCoordinateEquiv F T I e).toHomeomorph.symm.t2Space
  let := positiveSecondCountableTopology F T I e
  let := positiveLocallyCompactSpace F T I e
  let := normalizedPositiveHaarMeasure_isHaarMeasure F H T i hi I e hc
  let := normalizedPositiveHaarMeasure_sigmaFinite F H T i hi I e hc
  let := AdelicSiegelFactors.isFiniteMeasure_normOneRationalQuotientHaarMeasure_of_connectedReductive F H hH
  let Ht := adelicHeight F H rho
  have hHt : Continuous Ht := continuous_adelicHeight F H rho hN
  have hHt₀ (a : A) : 0 ≤ Ht a := zero_le_one.trans (one_le_adelicHeight F H rho hN a)
  let D : Set Pos := πP '' tsupport K
  have hD : IsCompact D := K.hasCompactSupport.image (πP).continuous
  obtain ⟨C, hC, hbd⟩ := exists_cuspidalNormOneKernelVector_weight_bound hH T i hi I e hc
    hDecay rho hN hrho K hK (pp '' D) (hD.image (pp).continuous) m
  obtain ⟨E₀, hE₀⟩ := (hD.image (hHt.comp (pp).continuous)).bddAbove
  obtain ⟨L₀, hL₀⟩ := (hD.image hd.norm).bddAbove
  let E := max E₀ 0
  let L := max L₀ 0
  have hE : 0 ≤ E := le_max_right _ _
  have hL : 0 ≤ L := le_max_right _ _
  let B := L * M * E ^ m * C
  have hB : 0 ≤ B := by positivity
  let W : Pos × X₁ → ℝ := fun p => D.indicator (fun _ => (1 : ℝ)) p.1
  have hW : Integrable W μf :=
    ((integrableOn_const hD.measure_lt_top.ne).integrable_indicator hD.measurableSet).comp_fst μ₁
  have hW₀ (p) : 0 ≤ W p := indicator_nonneg (fun _ _ => zero_le_one) _
  have hbdW (b : Pos) (p : Pos × X₁) : ‖Fv b p‖ ≤ (B * Ht (pp b) ^ m) * W p := by
    obtain ⟨t, ξ⟩ := p
    let y : A₁ := Quotient.out ξ
    let v := cuspidalNormOneKernelVector hH T i hi I e hc K ((y : A) * pp t)
    change ‖(d t * f ((y : A) * (pp b * pp t))) • v‖ ≤
      (B * Ht (pp b) ^ m) * D.indicator (fun _ => (1 : ℝ)) t
    by_cases ht : t ∈ D
    · obtain ⟨r, hr⟩ := hbd y
      specialize hr (pp t) ⟨t, ht, rfl⟩
      let a := rational F H r * (y : A)
      have hfr : f ((y : A) * (pp b * pp t)) = f (a * (pp b * pp t)) := by
        simpa only [a, mul_assoc] using (hfRat r ((y : A) * (pp b * pp t))).symm
      have hEt : Ht (pp t) ≤ E := (hE₀ ⟨t, ht, rfl⟩).trans (le_max_left _ _)
      have hLt : ‖d t‖ ≤ L := (hL₀ ⟨t, ht, rfl⟩).trans (le_max_left _ _)
      have hheight : Ht (a * (pp b * pp t)) ≤ Ht a * (Ht (pp b) * E) :=
        (adelicHeight_mul_le F H rho hN _ _).trans
          (mul_le_mul_of_nonneg_left ((adelicHeight_mul_le F H rho hN _ _).trans
            (mul_le_mul_of_nonneg_left hEt (hHt₀ _))) (hHt₀ _))
      have hfbd : ‖f (a * (pp b * pp t))‖ ≤ M * (Ht a ^ m * (Ht (pp b) ^ m * E ^ m)) := by
        rw [← mul_pow, ← mul_pow]
        exact (hfM _).trans (mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (hHt₀ _) hheight _) hM)
      rw [indicator_of_mem ht, mul_one, norm_smul, norm_mul, hfr]
      calc ‖d t‖ * ‖f (a * (pp b * pp t))‖ * ‖v‖
          ≤ L * (M * (Ht a ^ m * (Ht (pp b) ^ m * E ^ m))) * ‖v‖ := by
            exact mul_le_mul_of_nonneg_right (mul_le_mul hLt hfbd (norm_nonneg _) hL) (norm_nonneg _)
        _ = (L * M * E ^ m * Ht (pp b) ^ m) * (‖v‖ * Ht a ^ m) := by ring
        _ ≤ (L * M * E ^ m * Ht (pp b) ^ m) * C := by
            exact mul_le_mul_of_nonneg_left hr
              (mul_nonneg (mul_nonneg (mul_nonneg hL hM) (pow_nonneg hE _)) (pow_nonneg (hHt₀ _) _))
        _ = B * Ht (pp b) ^ m := by unfold B; ring
    · have hv : v = 0 := by
        apply cuspidalNormOneKernelVector_eq_zero_of_notMem
        change πP ((y : A) * pp t) ∉ D
        simpa only [map_mul, positiveFactor_normOne, positiveFactor_positivePointMap, one_mul] using ht
      simp [hv, ht]
  have hcon (b) := continuous_cuspidalFibreVectorIntegrand hH T i hi I e hc K f d hf hfRat hd b
  have hInt (b) : Integrable (Fv b) μf :=
    (hW.const_mul (B * Ht (pp b) ^ m)).mono' (hcon b).aestronglyMeasurable
      (Eventually.of_forall (hbdW b))
  refine ⟨hInt, ?_, B * (∫ p, W p ∂μf), mul_nonneg hB (integral_nonneg hW₀), fun b => ?_⟩
  · rw [continuous_iff_continuousAt]
    intro b
    obtain ⟨E', hE', hEb⟩ := exists_compact_mem_nhds b
    have hBC : Continuous (fun x : Pos => B * Ht (pp x) ^ m) :=
      continuous_const.mul ((hHt.comp (pp).continuous).pow m)
    obtain ⟨L', hL'⟩ := (hE'.image hBC).bddAbove
    refine continuousAt_of_dominated (bound := fun p => L' * W p)
      (Eventually.of_forall fun x => (hInt x).aestronglyMeasurable) ?_ (hW.const_mul L') ?_
    · filter_upwards [hEb] with x hx
      exact Eventually.of_forall fun p => (hbdW x p).trans
        (mul_le_mul_of_nonneg_right (hL' ⟨x, hx, rfl⟩) (hW₀ p))
    · refine Eventually.of_forall fun p => Continuous.continuousAt ?_
      exact (continuous_const.mul (hf.comp (continuous_const.mul
        ((pp).continuous.mul continuous_const)))).smul continuous_const
  · change ‖∫ p, Fv b p ∂μf‖ ≤ _
    calc ‖∫ p, Fv b p ∂μf‖ ≤ ∫ p, ‖Fv b p‖ ∂μf := norm_integral_le_integral_norm _
      _ ≤ ∫ p, (B * Ht (pp b) ^ m) * W p ∂μf :=
        integral_mono (hInt b).norm (hW.const_mul _) (hbdW b)
      _ = B * (∫ p, W p ∂μf) * Ht (pp b) ^ m := by rw [integral_const_mul]; ring

end Integral

end Langlands.Global
