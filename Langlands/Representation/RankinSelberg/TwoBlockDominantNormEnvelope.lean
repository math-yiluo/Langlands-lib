import Langlands.Representation.RankinSelberg.TwoBlockDominantTorusMajorant
import Langlands.Representation.RankinSelberg.TwoBlockDominantSliceSpectral

/-! # Integrable rectangle fibers and their actual raw-norm envelope -/

noncomputable section

namespace Langlands.RankinSelberg.TwoBlockDominantRectangular

open MeasureTheory GeneralLinear Whittaker HarmonicAnalysis TwoBlockDeformation
  TwoBlockJacquet TwoBlockConvergence TwoBlockLowerFixedSlice TwoBlockLowerUnipotentQuotient
open scoped BigOperators NNReal ENNReal

universe uF uV uW

variable {p : ℕ} [Fact p.Prime] {F : PadicField.{uF} p}

local instance normEnvelopeTopology : TopologicalSpace F.Carrier :=
  F.canonicalTopologicalData.topology
local instance normEnvelopeValuation : ValuativeRel F.Carrier :=
  F.canonicalTopologicalData.valuativeRel
local instance normEnvelopeLocalField : IsNonarchimedeanLocalField F.Carrier :=
  F.canonicalTopologicalData.localField
local instance normEnvelopeT2 : T2Space F.Carrier :=
  F.canonicalTopologicalData.fieldT2
local instance normEnvelopeSecondCountable : SecondCountableTopology F.Carrier :=
  F.canonicalTopologicalData.secondCountableTopology
local instance normEnvelopeMeasurable : MeasurableSpace F.Carrier := borel _
local instance normEnvelopeBorel : BorelSpace F.Carrier := ⟨rfl⟩
local instance normEnvelopeMatrixBorel (a b : ℕ) :
    BorelSpace (Matrix (Fin a) (Fin b) F.Carrier) :=
  inferInstanceAs (BorelSpace (Fin a → Fin b → F.Carrier))
local instance normEnvelopeMatrixSecondCountable (a b : ℕ) :
    SecondCountableTopology (Matrix (Fin a) (Fin b) F.Carrier) :=
  inferInstanceAs (SecondCountableTopology (Fin a → Fin b → F.Carrier))
local instance normEnvelopeRectanglesBorel (m : Fin 2 → ℕ) (j k : ℕ) :
    BorelSpace (Rectangles m j k F.Carrier) :=
  inferInstanceAs (BorelSpace (Matrix (Fin (m 0 + 1)) (Fin k) F.Carrier ×
    Matrix (Fin j) (Fin (m 1 + 1)) F.Carrier))

variable {t r j k : ℕ} {m : Fin 2 → ℕ} {h : ∑ i, (m i + 1) = t + 1}
variable {W : Fin 2 → Type uW} [∀ i, AddCommGroup (W i)] [∀ i, Module ℂ (W i)]
variable {σ : ∀ i, Representation ℂ (GeneralLinear (m i + 1) F.Carrier) (W i)}
variable {ψ : UnitaryAdditiveCharacter F.Carrier}

/-- The reference parameter removes the entire determinant weight. -/
theorem kernel_referenceParameter
    (ell : ∀ i, glInverseFunctionals ψ (m i) (σ i))
    (f : Sections F h σ) (Wtest : WhittakerFunctions ψ r)
    (hr : r = t + (j + k + 1)) (g : GeneralLinear (t + 1) F.Carrier)
    (x : Matrix (Fin (m 0 + 1)) (Fin k) F.Carrier)
    (y : Matrix (Fin j) (Fin (m 1 + 1)) F.Carrier) :
    kernel ell f Wtest hr (((j + k + 1 : ℕ) : ℂ) / 2 - (j : ℂ)) g x y =
      rawKernel ell f Wtest hr g x y := by
  unfold kernel
  rw [show (((j + k + 1 : ℕ) : ℂ) / 2 - (j : ℂ)) -
      ((j + k + 1 : ℕ) : ℂ) / 2 + (j : ℂ) = 0 by ring]
  simp [determinantWeight]

/-- Each simultaneous rectangle box has finite supplied Haar volume. -/
theorem rectangleMeasure_box_ne_top (ν : AdditiveHaarMeasure F.Carrier)
    (m : Fin 2 → ℕ) (j k e : ℕ) :
    rectangleMeasure F m j k ν
      ((box F (m 0 + 1) k e) ×ˢ (box F j (m 1 + 1) e)) ≠ ∞ := by
  rw [rectangleMeasure_box]
  exact ENNReal.mul_ne_top
    (ENNReal.pow_ne_top F.canonicalTopologicalData.isCompact_integers.measure_ne_top)
    (ENNReal.pow_ne_top (ENNReal.pow_ne_top (by simp)))

/-- Domination by a constant on the actual finite box proves both genuine
fiber integrability and a bound for the integral of the raw norm. -/
theorem fiber_integrable_normProfile_le_of_box
    (ν : AdditiveHaarMeasure F.Carrier)
    (ell : ∀ i, glInverseFunctionals ψ (m i) (σ i))
    (f : Sections F h σ) (Wtest : WhittakerFunctions ψ r)
    (hr : r = t + (j + k + 1)) (s : ℂ) (g : GeneralLinear (t + 1) F.Carrier)
    (e : ℕ) (A : ℝ)
    (hmeas : AEStronglyMeasurable
      (fun z : Rectangles m j k F.Carrier => kernel ell f Wtest hr s g z.1 z.2)
      (rectangleMeasure F m j k ν))
    (hbound : ∀ z : Rectangles m j k F.Carrier,
      ‖kernel ell f Wtest hr s g z.1 z.2‖ ≤ A)
    (hsupport : ∀ z : Rectangles m j k F.Carrier,
      kernel ell f Wtest hr s g z.1 z.2 ≠ 0 →
        z ∈ (box F (m 0 + 1) k e) ×ˢ (box F j (m 1 + 1) e)) :
    FiberIntegrable ν ell f Wtest hr s g ∧
      ‖representativeKernel ν ell f Wtest hr s g‖ ≤
        representativeNormProfile ν ell f Wtest hr s g ∧
      0 ≤ representativeNormProfile ν ell f Wtest hr s g ∧
      representativeNormProfile ν ell f Wtest hr s g ≤
        (rectangleMeasure F m j k ν).real
          ((box F (m 0 + 1) k e) ×ˢ (box F j (m 1 + 1) e)) * A := by
  classical
  let S := (box F (m 0 + 1) k e) ×ˢ (box F j (m 1 + 1) e)
  have hS : MeasurableSet S := measurableSet_rectangle_box F m j k e
  have hI : Integrable (S.indicator (fun _ : Rectangles m j k F.Carrier => A))
      (rectangleMeasure F m j k ν) :=
    (integrable_indicator_iff hS).mpr
      (integrableOn_const (C := A) (rectangleMeasure_box_ne_top ν m j k e))
  have hdom : ∀ z : Rectangles m j k F.Carrier,
      ‖kernel ell f Wtest hr s g z.1 z.2‖ ≤ S.indicator (fun _ => A) z := by
    intro z
    by_cases hz : z ∈ S
    · simpa only [Set.indicator_of_mem hz] using hbound z
    · have hzero : kernel ell f Wtest hr s g z.1 z.2 = 0 := by
        by_contra hne
        exact hz (hsupport z hne)
      simp only [Set.indicator_of_notMem hz, hzero, norm_zero, le_refl]
  have hint := hI.mono' hmeas (Filter.Eventually.of_forall hdom)
  refine ⟨hint, norm_integral_le_integral_norm _, integral_nonneg (fun _ => norm_nonneg _), ?_⟩
  calc
    _ ≤ ∫ z, S.indicator (fun _ => A) z ∂rectangleMeasure F m j k ν :=
      integral_mono_ae hint.norm hI (Filter.Eventually.of_forall hdom)
    _ = _ := by rw [integral_indicator_const _ hS, smul_eq_mul]

/-- The real volume retains the exact scalar Haar normalization. -/
theorem rectangleMeasure_real_box (ν : AdditiveHaarMeasure F.Carrier)
    (m : Fin 2 → ℕ) (j k e : ℕ) :
    (rectangleMeasure F m j k ν).real
      ((box F (m 0 + 1) k e) ×ˢ (box F j (m 1 + 1) e)) =
      (ν.measure.real (F.canonicalTopologicalData.Integers : Set F.Carrier)) ^
          ((m 0 + 1) * k + j * (m 1 + 1)) *
        ((F.canonicalTopologicalData.residueCardinality : ℝ) ^
          ((m 0 + 1) * k + j * (m 1 + 1))) ^ e := by
  simp only [measureReal_def, rectangleMeasure_box, ENNReal.toReal_mul,
    ENNReal.toReal_pow, ENNReal.toReal_natCast]

/-- A loose common dimension bound is independent of the complementary
rectangle dimensions. -/
theorem rectangle_dimension_le (h : ∑ i, (m i + 1) = t + 1)
    (hr : r = t + (j + k + 1)) :
    (m 0 + 1) * k + j * (m 1 + 1) ≤ 2 * (r + 1) * (r + 1) := by
  have hm : m 0 + 1 + (m 1 + 1) = t + 1 := by
    simpa only [Fin.sum_univ_two] using h
  have h0 : m 0 + 1 ≤ r + 1 := by omega
  have h1 : m 1 + 1 ≤ r + 1 := by omega
  have hj : j ≤ r + 1 := by omega
  have hk : k ≤ r + 1 := by omega
  calc
    _ ≤ (r + 1) * (r + 1) + (r + 1) * (r + 1) :=
      Nat.add_le_add (Nat.mul_le_mul h0 hk) (Nat.mul_le_mul hj h1)
    _ = _ := by ring

/-- The varying part of box volume admits one base before all `j,k`. -/
theorem rectangleMeasure_real_box_le (ν : AdditiveHaarMeasure F.Carrier)
    (h : ∑ i, (m i + 1) = t + 1) (hr : r = t + (j + k + 1))
    (N L : ℕ) :
    (rectangleMeasure F m j k ν).real
      ((box F (m 0 + 1) k (N + L)) ×ˢ (box F j (m 1 + 1) (N + L))) ≤
      ((ν.measure.real (F.canonicalTopologicalData.Integers : Set F.Carrier)) ^
          ((m 0 + 1) * k + j * (m 1 + 1)) *
        ((F.canonicalTopologicalData.residueCardinality : ℝ) ^
          ((m 0 + 1) * k + j * (m 1 + 1))) ^ N) *
      ((F.canonicalTopologicalData.residueCardinality : ℝ) ^
        (2 * (r + 1) * (r + 1))) ^ L := by
  rw [rectangleMeasure_real_box, pow_add _ N L, ← mul_assoc]
  have hq : (1 : ℝ) ≤ F.canonicalTopologicalData.residueCardinality := by
    exact_mod_cast F.canonicalTopologicalData.residueCardinality_gt_one.le
  gcongr
  exact rectangle_dimension_le h hr

variable {V : Type uV} [AddCommGroup V] [Module ℂ V]

/-- One geometric base bounds the actual integrated raw norm; it precedes the
twist, section, both complementary rectangle dimensions and test vector. -/
def IsKernelNormTorusEnvelope
    (ν : AdditiveHaarMeasure F.Carrier) (h : ∑ i, (m i + 1) = t + 1)
    (ψ : UnitaryAdditiveCharacter F.Carrier)
    (π : Representation ℂ (GeneralLinear (r + 1) F.Carrier) V)
    (lambda : glFunctionals ψ r π)
    (τ : ∀ i, Representation ℂ (GeneralLinear (m i + 1) F.Carrier) (W i))
    (ell : ∀ i, glInverseFunctionals ψ (m i) (τ i))
    (a : Fin t) (B : ℝ) : Prop :=
  ∀ (u : ℝ) (f : Sections F h (twoBlockOppositeTwistBlocks F m τ u))
    (j k : ℕ) (hr : r = t + (j + k + 1))
    (Wtest : (coefficientModel π lambda).toSubmodule),
    ∃ (C : ℝ) (M : ℕ), 0 ≤ C ∧
      ∀ (lam : Fin (t + 1) → ℤ) (c : GeneralLinear (t + 1) F.Carrier),
        c ∈ integralOpen F t →
        let ellu := fun i => twoBlockOppositeTwistFunctional F m ψ τ u i (ell i)
        let g := (blockRotation h F.Carrier)⁻¹ * Iwasawa.torus
          (LocalFactor.PadicAbelian.uniformizerUnit F.canonicalTopologicalData) lam * c
        let s0 := ((j + k + 1 : ℕ) : ℂ) / 2 - (j : ℂ)
        FiberIntegrable ν ellu f Wtest.val hr s0 g ∧
        ‖representativeKernel ν ellu f Wtest.val hr s0 g‖ ≤
          representativeNormProfile ν ellu f Wtest.val hr s0 g ∧
        0 ≤ representativeNormProfile ν ellu f Wtest.val hr s0 g ∧
        representativeNormProfile ν ellu f Wtest.val hr s0 g ≤
          C * B ^ torusSize lam *
            (F.canonicalTopologicalData.residueCardinality : ℝ) ^
              (-u * (twistDegree (Finset.Iic a.castSucc) lam : ℝ)) ∧
        (representativeNormProfile ν ellu f Wtest.val hr s0 g ≠ 0 →
          OppositeCone M (Finset.Iic a.castSucc) lam)

/-- Finite-volume domination and the raw torus majorant give genuine rectangle
fiber convergence and a uniform geometric envelope for its raw-norm integral. -/
theorem exists_kernelNorm_torus_envelope
    (ν : AdditiveHaarMeasure F.Carrier) (h : ∑ i, (m i + 1) = t + 1)
    (ψ : UnitaryAdditiveCharacter F.Carrier)
    (π : Representation ℂ (GeneralLinear (r + 1) F.Carrier) V)
    (hπ : IsOfWhittakerType r (standardCharacter ψ r) π)
    (lambda : glFunctionals ψ r π)
    (τ : ∀ i, Representation ℂ (GeneralLinear (m i + 1) F.Carrier) (W i))
    (hτ : ∀ i, IsOfWhittakerType (m i) (standardCharacter ψ (m i)) (τ i))
    (ell : ∀ i, glInverseFunctionals ψ (m i) (τ i))
    (a : Fin t) (ha : a.val = m 1) :
    ∃ B : ℝ, 1 ≤ B ∧ IsKernelNormTorusEnvelope ν h ψ π lambda τ ell a B := by
  obtain ⟨B, hB, hraw⟩ := exists_rawKernel_torus_majorant F h ψ π hπ lambda τ hτ ell a ha
  let q : ℝ := F.canonicalTopologicalData.residueCardinality
  let D : ℝ := q ^ (2 * (r + 1) * (r + 1))
  have hq : 1 ≤ q := by
    dsimp only [q]
    exact_mod_cast F.canonicalTopologicalData.residueCardinality_gt_one.le
  refine ⟨B * D, one_le_mul_of_one_le_of_one_le hB (one_le_pow₀ hq),
    fun u f j k hr Wtest => ?_⟩
  obtain ⟨C, N, M, hC0, hC⟩ := hraw u f j k hr Wtest
  let Cv : ℝ := (ν.measure.real (F.canonicalTopologicalData.Integers : Set F.Carrier)) ^
      ((m 0 + 1) * k + j * (m 1 + 1)) *
    (q ^ ((m 0 + 1) * k + j * (m 1 + 1))) ^ N
  have hCv : 0 ≤ Cv := by dsimp only [Cv]; positivity
  refine ⟨Cv * C, M, mul_nonneg hCv hC0, fun lam c hc => ?_⟩
  dsimp only
  let ellu := fun i => twoBlockOppositeTwistFunctional F m ψ τ u i (ell i)
  let g := (blockRotation h F.Carrier)⁻¹ * Iwasawa.torus
    (LocalFactor.PadicAbelian.uniformizerUnit F.canonicalTopologicalData) lam * c
  let s0 : ℂ := ((j + k + 1 : ℕ) : ℂ) / 2 - (j : ℂ)
  have hmeas : AEStronglyMeasurable
      (fun z : Rectangles m j k F.Carrier => kernel ellu f Wtest.val hr s0 g z.1 z.2)
      (rectangleMeasure F m j k ν) :=
    ((continuous_kernel ellu f π hπ.1.1 lambda Wtest hr s0).comp
      (continuous_const.prodMk continuous_id)).measurable.aestronglyMeasurable
  have hb : ∀ z : Rectangles m j k F.Carrier,
      ‖kernel ellu f Wtest.val hr s0 g z.1 z.2‖ ≤
        C * B ^ torusSize lam * q ^
          (-u * (twistDegree (Finset.Iic a.castSucc) lam : ℝ)) := by
    intro z
    rw [kernel_referenceParameter]
    exact (hC lam c z.1 z.2 hc).1
  have hs : ∀ z : Rectangles m j k F.Carrier,
      kernel ellu f Wtest.val hr s0 g z.1 z.2 ≠ 0 →
      z ∈ (box F (m 0 + 1) k (N + torusSize lam)) ×ˢ
        (box F j (m 1 + 1) (N + torusSize lam)) := by
    intro z hz
    rw [kernel_referenceParameter] at hz
    exact (hC lam c z.1 z.2 hc).2 hz |>.2
  obtain ⟨hi, hn, hp0, hp⟩ := fiber_integrable_normProfile_le_of_box ν ellu f Wtest.val
    hr s0 g (N + torusSize lam) _ hmeas hb hs
  refine ⟨hi, hn, hp0, hp.trans ?_, ?_⟩
  · calc
      _ ≤ (Cv * D ^ torusSize lam) *
          (C * B ^ torusSize lam * q ^
            (-u * (twistDegree (Finset.Iic a.castSucc) lam : ℝ))) :=
        mul_le_mul_of_nonneg_right
          (rectangleMeasure_real_box_le ν h hr N (torusSize lam)) (by positivity)
      _ = _ := by rw [mul_pow]; ring
  · intro hpne
    by_contra hcone
    have hz : ∀ z : Rectangles m j k F.Carrier,
        kernel ellu f Wtest.val hr s0 g z.1 z.2 = 0 := by
      intro z
      rw [kernel_referenceParameter]
      by_contra hne
      exact hcone ((hC lam c z.1 z.2 hc).2 hne).1
    apply hpne
    change representativeNormProfile ν ellu f Wtest.val hr s0 g = 0
    simp only [representativeNormProfile, hz, norm_zero, integral_zero]

end Langlands.RankinSelberg.TwoBlockDominantRectangular
