import Langlands.Representation.Archimedean.RealCartanTraceLocalization
import Langlands.Representation.Archimedean.RealCartanScaledPeakIntegral
import Mathlib.MeasureTheory.Measure.Lebesgue.EqHaar

/-! # The transverse limit of the weighted compact Cartan trace -/

noncomputable section

open Matrix MeasureTheory Set Filter Metric Module
open scoped Matrix.Norms.Operator Topology ENNReal

namespace Langlands.Archimedean.RealCartanTransverseLimit

open RealCartanAngularFrame RealCartanArgumentJacobian RealCartanCompactSupport
  RealCartanLowerCoordinates RealCartanPeakTest RealCartanScaledPeakIntegral
  RealCartanTraceCoordinates RealCartanTraceLocalization RealLeviChart RealLeviCompactChart
  RealPrincipalSeriesDuality

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

local notation "K" n:max => Matrix.unitaryGroup (Fin n) ℝ
local notation "M" n:max => Matrix (Fin n) (Fin n) ℝ
local notation "L" n:max => (LowerIndex n → ℝ)

attribute [local instance] measurableSpaceK RealLeviBlockHaar.secondCountableTopology_GL
  RealLeviBlockHaar.secondCountableTopology_O
local instance borelSpaceK (n : ℕ) : BorelSpace (unitaryCompact ℝ n) := ⟨rfl⟩

/-- The cone peak in lower coordinates with its diagonal cutoff. -/
def coneTest (n : ℕ) (ε : ℝ) : C(K n, ℂ) where
  toFun k := (diagonalCutoff k : ℂ) * (cone (ε⁻¹ • lowerProjection n (k : M n)) : ℂ)
  continuous_toFun := by
    have hL := ((lowerProjection n).continuous.comp (continuous_subtype_val : Continuous (Subtype.val : K n → M n)))
    have hε := (continuous_const (y := ε⁻¹)).smul hL
    have h := continuous_cone.comp hε
    exact (Complex.continuous_ofReal.comp (continuous_diagonalCutoff n)).mul
      (Complex.continuous_ofReal.comp h)

/-- The same cone peak with Euclidean inverse-volume scaling. -/
def scaledConeTest (n : ℕ) (ε : ℝ) : C(K n, ℂ) :=
  (ε ^ finrank ℝ (L n))⁻¹ • coneTest n ε

theorem eventually_support_scaledConeTest_subset (n : ℕ) {U : Set (K n)}
    (hU : IsOpen U) (h1 : 1 ∈ U) :
    ∀ᶠ ε in 𝓝[>] (0 : ℝ), Function.support (scaledConeTest n ε) ⊆ U := by
  filter_upwards [eventually_support_rawTest_subset n hU h1, self_mem_nhdsWithin] with ε hε hp k hk
  have hpos : 0 < ε := hp
  apply hε
  intro hz
  have hzero : diagonalCutoff k * max 0 (ε - ‖lowerProjection n (k : M n)‖) = 0 := hz
  rcases mul_eq_zero.mp hzero with h | h
  · exact hk (by simp [scaledConeTest, coneTest, h])
  · have hle : ε ≤ ‖lowerProjection n (k : M n)‖ := sub_nonpos.mp
      ((le_max_right (0 : ℝ) _).trans_eq h)
    have hb : 1 ≤ ‖ε⁻¹ • lowerProjection n (k : M n)‖ := by
      rw [norm_smul, Real.norm_of_nonneg (inv_nonneg.mpr hpos.le), inv_mul_eq_div, le_div_iff₀ hpos,
        one_mul]
      exact hle
    exact hk (by simp [scaledConeTest, coneTest, cone_eq_zero_of_one_le hb])

/-- Lebesgue mass of the cone peak in the common ambient lower entries. -/
def coneMass (n : ℕ) : ℝ := ∫ z : L n, cone z ∂volume

theorem coneMass_pos (n : ℕ) : 0 < coneMass n := by
  have hcompact : HasCompactSupport (cone : L n → ℝ) := by
    apply HasCompactSupport.intro' (isCompact_closedBall (0 : L n) 1) isClosed_closedBall
    intro z hz
    exact cone_eq_zero_of_one_le (le_of_not_ge (fun h => hz (mem_closedBall_zero_iff.mpr h)))
  exact continuous_cone.integral_pos_of_hasCompactSupport_nonneg_nonzero
    (μ := volume) (x := 0) hcompact cone_nonneg (by simp [cone])

section Transverse

variable {c : ℕ} (sz : Fin c → ℕ)

local notation "N" => ∑ i, sz i
local notation "H" => LeviFrame sz
local notation "G" => Langlands.GeneralLinear N ℝ
local notation "E" => ((Coord sz → ℝ) × (WithinIndex sz → ℝ))

private def lowerEnd (D : E →L[ℝ] L N) : L N →L[ℝ] L N :=
  D.comp ((joinLower sz).symm : L N →L[ℝ] E)

private theorem injective_of_det_ne_zero (D : E →L[ℝ] L N) (hD : (lowerEnd sz D).det ≠ 0) :
    Function.Injective D := by
  have hker : LinearMap.ker (lowerEnd sz D).toLinearMap = ⊥ :=
    not_not.mp (mt LinearMap.det_eq_zero_iff_ker_ne_bot.mpr hD)
  have hinj : Function.Injective (lowerEnd sz D) := LinearMap.ker_eq_bot.mp hker
  exact fun x y h => (joinLower sz).injective (hinj (by simpa [lowerEnd] using h))

private theorem integral_linearCone (D : E →L[ℝ] L N) (hD : (lowerEnd sz D).det ≠ 0) (v : ℂ) :
    (∫ z : E, (cone (D z) : ℂ) * v ∂volume) =
      (coneMass N : ℂ) * ((|(lowerEnd sz D).det|⁻¹ : ℝ) : ℂ) * v := by
  let A := lowerEnd sz D
  let f (z : L N) := (cone z : ℂ) * v
  have hf : Continuous f := (Complex.continuous_ofReal.comp continuous_cone).mul continuous_const
  have hmap := Real.map_linearMap_volume_pi_eq_smul_volume_pi (f := A.toLinearMap) hD
  rw [abs_inv] at hmap
  calc
    _ = ∫ z : L N, f (A z) ∂volume := by
      have he := (measurePreserving_joinLower sz).integral_comp
        (joinLower sz).toHomeomorph.measurableEmbedding (fun z : L N => f (A z))
      simpa only [A, lowerEnd, ContinuousLinearMap.comp_apply, ContinuousLinearEquiv.coe_coe,
        ContinuousLinearEquiv.symm_apply_apply, f] using he
    _ = ∫ z : L N, f z ∂(volume : Measure (L N)).map A.toLinearMap :=
      (integral_map A.continuous.aemeasurable hf.aestronglyMeasurable).symm
    _ = _ := by
      rw [hmap, integral_smul_measure, ENNReal.toReal_ofReal (by positivity), Complex.real_smul]
      simp only [f, integral_mul_const, integral_complex_ofReal, coneMass]
      ring

set_option maxHeartbeats 500000 in
private theorem local_limit (g : G) (w : K N) (R : H) (η : C(K N, ℂ))
    (W : C(K N × H, ℂ)) (F : H × E → E →L[ℝ] L N) (hF : Continuous F)
    (hderiv : ∀ κ z, HasFDerivAt (projectedArgument sz g w R κ) (F (κ, z)) z)
    (h0 : ∀ κ, projectedArgument sz g w R κ 0 = 0)
    (hdet : ∀ κ, (lowerEnd sz (F (κ, 0))).det ≠ 0)
    (hcenter : ∀ κ, placedArgument sz g w R κ 0 = 1)
    (hη : ∀ κ, η (blockFrame sz κ * w) = 1) :
    ∃ r > 0, ∀ s > 0, s ≤ r →
      Tendsto (fun ε : ℝ => ∫ κ, ∫ z in closedBall (0 : E) s,
        localizedWeight sz w R η W κ z * scaledConeTest N ε (placedArgument sz g w R κ z)
        ∂volume ∂frameMeasure sz) (𝓝[>] (0 : ℝ))
        (𝓝 ((coneMass N : ℂ) * ∫ κ, ((|(lowerEnd sz (F (κ, 0))).det|⁻¹ : ℝ) : ℂ) *
          W (blockFrame sz κ * w, fixedLeftFrame sz R κ) ∂frameMeasure sz)) := by
  let D (κ : H) := F (κ, 0)
  let f := projectedArgument sz g w R
  let A (κ : H) (z : E) := (diagonalCutoff (placedArgument sz g w R κ z) : ℂ) *
    localizedWeight sz w R η W κ z
  have hA : Continuous (Function.uncurry A) :=
    (Complex.continuous_ofReal.comp ((continuous_diagonalCutoff N).comp
      (continuous_placedArgument sz g w R))).mul (continuous_localizedWeight sz w R η W)
  have hinj (κ : H) : Function.Injective (D κ) := injective_of_det_ne_zero sz _ (hdet κ)
  have hD : Continuous D := hF.comp (continuous_id.prodMk continuous_const)
  obtain ⟨r, hr, m, hm, hb⟩ := exists_nonlinear_bound f F hF hderiv h0 hinj
  obtain ⟨m', hm', hb'⟩ := exists_linear_bound D hD hinj
  let ρ := min m m'
  have hρ : 0 < ρ := lt_min hm hm'
  refine ⟨r, hr, fun s hs hsr => ?_⟩
  have hstatement : RealCartanScaledPeakIntegralStatement H E (L N) := realCartanScaledPeakIntegral
  have : (volume : Measure (Coord sz → ℝ)).IsAddHaarMeasure := isAddHaarMeasure_volume_pi _
  have : (volume : Measure (WithinIndex sz → ℝ)).IsAddHaarMeasure := isAddHaarMeasure_volume_pi _
  have : (volume : Measure E).IsAddHaarMeasure := by
    change ((volume : Measure (Coord sz → ℝ)).prod (volume : Measure (WithinIndex sz → ℝ))).IsAddHaarMeasure
    infer_instance
  have ht := hstatement (frameMeasure sz) volume f D A s ρ (continuous_projectedArgument sz g w R) hD hA h0
    (fun κ => hderiv κ 0) hs hρ
    (fun κ z hz => (mul_le_mul_of_nonneg_right (min_le_left m m') (norm_nonneg z)).trans
      (hb κ z (hz.trans hsr)))
    (fun κ z => (mul_le_mul_of_nonneg_right (min_le_right m m') (norm_nonneg z)).trans (hb' κ z))
  have hdim := (joinLower sz).toLinearEquiv.finrank_eq
  have hfun (ε : ℝ) : (∫ κ, ∫ z in closedBall (0 : E) s,
      localizedWeight sz w R η W κ z * scaledConeTest N ε (placedArgument sz g w R κ z)
      ∂volume ∂frameMeasure sz) = (ε ^ finrank ℝ E)⁻¹ •
        (∫ κ, ∫ z in closedBall (0 : E) s, (cone (ε⁻¹ • f κ z) : ℂ) * A κ z ∂volume
          ∂frameMeasure sz) := by
    rw [hdim, ← integral_smul]
    apply integral_congr_ae
    exact ae_of_all _ fun κ => by
      dsimp only
      rw [← integral_smul]
      apply integral_congr_ae
      exact ae_of_all _ fun z => by
        simp only [scaledConeTest, coneTest, ContinuousMap.smul_apply, ContinuousMap.coe_mk,
          Complex.real_smul, A, f, projectedArgument]
        ring
  simp_rw [hfun]
  have hmid (κ : H) : A κ 0 = W (blockFrame sz κ * w, fixedLeftFrame sz R κ) := by
    simp [A, hcenter κ, localizedWeight, hη κ, chartWeight_zero]
  have hfinal (κ : H) : (∫ z : E, (cone (D κ z) : ℂ) * A κ 0 ∂volume) =
      (coneMass N : ℂ) * (((|(lowerEnd sz (F (κ, 0))).det|⁻¹ : ℝ) : ℂ) *
        W (blockFrame sz κ * w, fixedLeftFrame sz R κ)) := by
    rw [hmid, integral_linearCone sz _ (hdet κ), mul_assoc]
  simpa only [hfinal, integral_const_mul] using ht

end Transverse

/-- In each fixed chart the rescaled trace is the central weight over the
absolute transverse determinant. The common chart coefficient is independent
of the selected cosets, their Cartan matrix, and the weight. -/
def RealCartanTransverseLimitStatement : Prop :=
  ∀ (c : ℕ) (sz : Fin c → ℕ),
    let n := ∑ i, sz i
    let H := LeviFrame sz
    ∃ C : ℝ, 0 < C ∧
      ∀ (ι : Type) [Fintype ι] (g : Langlands.GeneralLinear n ℝ) (w : ι → K n) (R : ι → H)
        (d : ι → Fin n → ℝ) (D : ι → Langlands.GeneralLinear n ℝ),
        (∀ i, sz i = 1 ∨ sz i = 2) → (∀ i j, 0 < d i j) →
        (∀ i, (D i : M n) = diagonal (d i)) →
        (∀ i, Unitary.toUnits (w i) * g = D i * Unitary.toUnits (blockFrame sz (R i) * w i)) →
        (∀ i κ, Unitary.toUnits (blockFrame sz κ) * D i = D i * Unitary.toUnits (blockFrame sz κ)) →
        Pairwise (fun i j => Disjoint (range (fun κ => blockFrame sz κ * w i))
          (range (fun κ => blockFrame sz κ * w j))) →
        (∀ y h, compactArgument g y (blockFrame sz h) = 1 →
          ∃ i, y ∈ range (fun κ => blockFrame sz κ * w i)) →
        (∀ i κ h, compactArgument g (blockFrame sz κ * w i) (blockFrame sz h) = 1 ↔
          h = fixedLeftFrame sz (R i) κ) →
        (∀ i κ, (argumentLowerEnd sz (d i) (blockFrame sz (fixedLeftFrame sz (R i) κ))
          (blockFrame sz κ * w i)).det ≠ 0) →
        ∀ W : C(K n × H, ℂ), Tendsto (fun ε => weightedIntegral sz g W (scaledConeTest n ε))
          (𝓝[>] (0 : ℝ)) (𝓝 ((C : ℂ) * (coneMass n : ℂ) * ∑ i, ∫ κ,
            ((|(argumentLowerEnd sz (d i) (blockFrame sz (fixedLeftFrame sz (R i) κ))
              (blockFrame sz κ * w i)).det|⁻¹ : ℝ) : ℂ) *
              W (blockFrame sz κ * w i, fixedLeftFrame sz (R i) κ) ∂frameMeasure sz))

set_option maxHeartbeats 750000 in
theorem realCartanTransverseLimit : RealCartanTransverseLimitStatement := by
  intro c sz n H
  obtain ⟨C, hC, hl⟩ := realCartanTraceLocalization c sz
  refine ⟨C * frameCoefficient sz, mul_pos hC (frameCoefficient_pos sz), ?_⟩
  intro ι _ g w R d D hsize hd hD hw hk hdisj hfix hcenter hdet W
  obtain ⟨η, hη, hloc⟩ := hl ι g w R hsize hdisj hfix hcenter
  let J (i : ι) (κ : H) := argumentLowerEnd sz (d i)
    (blockFrame sz (fixedLeftFrame sz (R i) κ)) (blockFrame sz κ * w i)
  let I (i : ι) := ∫ κ, ((|(J i κ).det|⁻¹ : ℝ) : ℂ) *
    W (blockFrame sz κ * w i, fixedLeftFrame sz (R i) κ) ∂frameMeasure sz
  let E := (Coord sz → ℝ) × (WithinIndex sz → ℝ)
  let P (s : ℝ) (i : ι) (ε : ℝ) := ∫ κ, ∫ z in closedBall (0 : E) s,
    localizedWeight sz (w i) (R i) (η i) W κ z * scaledConeTest n ε
      (placedArgument sz g (w i) (R i) κ z) ∂volume ∂frameMeasure sz
  have hlocal (i : ι) : ∃ r > 0, ∀ s > 0, s ≤ r → Tendsto (P s i) (𝓝[>] (0 : ℝ))
      (𝓝 ((coneMass n : ℂ) * I i)) := by
    obtain ⟨F, hF, hderiv, hzero⟩ := realCartanTraceCoordinates c sz g (D i) (w i) (R i) (d i)
      hsize (hd i) (hD i) (hw i) (hk i)
    have hJ (κ : H) : lowerEnd sz (F (κ, 0)) = J i κ := by
      rw [(hzero κ).2]
      rfl
    have h0 (κ : H) : placedArgument sz g (w i) (R i) κ 0 = 1 := by
      simpa only [placedArgument, Prod.fst_zero, Prod.snd_zero, placedFrame_zero, placedLeftFrame_zero]
        using (hcenter i κ _).mpr rfl
    have h := local_limit sz g (w i) (R i) (η i) W F hF hderiv (fun κ => (hzero κ).1)
      (fun κ => (hJ κ).symm ▸ hdet i κ) h0 (hη i)
    simpa only [P, I, hJ] using h
  choose r hr hR using hlocal
  have hm : ∀ᶠ s in 𝓝[>] (0 : ℝ), ∀ i, s ∈ Ioo 0 (r i) :=
    eventually_all.mpr fun i => Ioo_mem_nhdsGT (hr i)
  have hsmall : ∀ᶠ s in 𝓝[>] (0 : ℝ), s ∈ Ioo 0 (min 1 Real.pi) :=
    Ioo_mem_nhdsGT (lt_min zero_lt_one Real.pi_pos)
  obtain ⟨s, hs, hsR⟩ := (hsmall.and hm).exists
  have htr := hloc W (scaledConeTest n) (fun U => eventually_support_scaledConeTest_subset n (U := U))
    s hs.1 (hs.2.le.trans (min_le_left _ _)) (hs.2.le.trans (min_le_right _ _))
  have hsum := tendsto_finsetSum Finset.univ fun i _ => hR i s hs.1 (hsR i).2.le
  have hscale := (tendsto_const_nhds (x := (C : ℂ) * (frameCoefficient sz : ℂ))).mul hsum
  have htarget : ((C : ℂ) * (frameCoefficient sz : ℂ)) * ∑ i, (coneMass n : ℂ) * I i =
      ((C * frameCoefficient sz : ℝ) : ℂ) * (coneMass n : ℂ) * ∑ i, I i := by
    rw [← Finset.mul_sum, Complex.ofReal_mul, mul_assoc ((C : ℂ) * (frameCoefficient sz : ℂ))]
  rw [htarget] at hscale
  exact hscale.congr' (Filter.EventuallyEq.symm htr)

end Langlands.Archimedean.RealCartanTransverseLimit
