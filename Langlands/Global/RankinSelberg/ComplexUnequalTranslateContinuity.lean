import Langlands.Global.RankinSelberg.ComplexUnequalTranslateGrowth
import Langlands.Global.RankinSelberg.ComplexNormalizedApproximation

/-! # Continuous parameter dependence of translated unequal normalizations -/

noncomputable section

open Filter MeasureTheory Set
open scoped Matrix.Norms.Operator NNReal Topology

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

namespace Langlands.Global.RankinSelbergGlobal.ComplexUnequalWeightedTranslation

open ArchimedeanLocal Langlands.LocalFactor.Archimedean
open Langlands.RankinSelberg (LeftUnipotentQuotient)
open ArchimedeanInverseMellin (rpow_le_add)
open ComplexJacquet (HasComplexPairNormalizedGrowth complexCentralSign_sq CauchyOnRightVerticalLines
  complexPairNormalizedApproximation)
open ComplexUnequalFamily (HalfPlaneDomination differentiableOn_integral_of_halfPlaneDomination
  continuous_ordinaryKernel continuous_dualKernel)
open ComplexUnequalMellinReduction (quotientDetAbs quotientDetAbs_pos complexUnequalIntegrand_eq_mul
  complexUnequalDualKernel_eq_mul)
open Langlands.GeneralDirichlet (eqOn_halfPlane)

attribute [local instance] archimedeanEquationComplexGLMeasurable archimedeanEquationComplexGLBorel
  archimedeanEquationComplexNMeasurable archimedeanEquationComplexNBorel
  archimedeanEquationComplexQMeasurable archimedeanEquationComplexQBorel

local notation "G" => fun n => Langlands.GeneralLinear n ℂ
local notation "Q" => fun t => LeftUnipotentQuotient t ℂ
local notation "ρ" => ArchimedeanLocal.translateFunction

private theorem mellin_sequence {X : Type*} [MeasurableSpace X] (μ : Measure X)
    (f : Option ℕ → X → ℂ) (δ : X → ℝ) (hδ : ∀ x, 0 < δ x) (σ : ℝ)
    (hM : ∀ j (s : ℂ), AEStronglyMeasurable (fun x => f j x * (δ x : ℂ) ^ s) μ)
    (hdom : ∀ b : ℝ, σ ≤ b → ∃ B : X → ℝ, Integrable B μ ∧
      ∀ j x, ‖f j x‖ * δ x ^ b ≤ B x)
    (hlim : ∀ x, Tendsto (fun n => f (some n) x) atTop (𝓝 (f none x))) :
    let I (j : Option ℕ) (s : ℂ) := ∫ x, f j x * (δ x : ℂ) ^ s ∂μ
    (∀ j, DifferentiableOn ℂ (I j) {s : ℂ | σ < s.re}) ∧
      CauchyOnRightVerticalLines σ (fun n => I (some n)) ∧
      ∀ s : ℂ, σ < s.re → Tendsto (fun n => I (some n) s) atTop (𝓝 (I none s)) := by
  let F (j : Option ℕ) (s : ℂ) (x : X) := f j x * (δ x : ℂ) ^ s
  intro I
  have hNorm (j : Option ℕ) (s : ℂ) (x : X) : ‖F j s x‖ = ‖f j x‖ * δ x ^ s.re := by
    dsimp only [F]
    rw [norm_mul, Complex.norm_cpow_eq_rpow_re_of_pos (hδ x)]
  obtain ⟨B₀, hB₀, hb₀⟩ := hdom σ le_rfl
  have hD (j : Option ℕ) : DifferentiableOn ℂ (I j) {s : ℂ | σ < s.re} := by
    have hBound : HalfPlaneDomination μ (univ : Set ℂ) id (F j) σ := by
      intro τ
      obtain ⟨B, hB, hb⟩ := hdom (max σ τ) (le_max_left _ _)
      refine ⟨fun x => B₀ x + B x, hB₀.add hB, fun s _ hs ht x => ?_⟩
      rw [hNorm]
      calc
        _ ≤ ‖f j x‖ * (δ x ^ σ + δ x ^ max σ τ) :=
          mul_le_mul_of_nonneg_left (rpow_le_add (hδ x) hs.le (ht.trans (le_max_right _ _))) (norm_nonneg _)
        _ = ‖f j x‖ * δ x ^ σ + ‖f j x‖ * δ x ^ max σ τ := mul_add _ _ _
        _ ≤ _ := add_le_add (hb₀ j x) (hb j x)
    have hDiff (x : X) : Differentiable ℂ (fun s => F j s x) :=
      (differentiable_id.const_cpow (Or.inl (Complex.ofReal_ne_zero.mpr (hδ x).ne'))).const_mul _
    have hHol := (differentiableOn_integral_of_halfPlaneDomination (s := id) isOpen_univ differentiable_id
      (hM j) (fun x => (hDiff x).differentiableOn) hBound).2
    exact hHol.mono fun s hs => ⟨mem_univ s, hs⟩
  have hPt (s : ℂ) (x : X) : Tendsto (fun n => F (some n) s x) atTop (𝓝 (F none s x)) :=
    (hlim x).mul tendsto_const_nhds
  refine ⟨hD, ?_, fun s hs => ?_⟩
  · intro b hb ε hε
    obtain ⟨B, hB, hBnd⟩ := hdom b hb.le
    let z : ℂ := b
    have hz (j : Option ℕ) (x : X) : ‖F j z x‖ ≤ B x := by
      rw [hNorm, Complex.ofReal_re]
      exact hBnd j x
    have hzσ (j : Option ℕ) : Integrable (F j z) μ := hB.mono' (hM j z) (ae_of_all _ (hz j))
    let R (n : ℕ) := ∫ x, ‖F (some n) z x - F none z x‖ ∂μ
    have hR : Tendsto R atTop (𝓝 0) := by
      have h := tendsto_integral_of_dominated_convergence
        (F := fun n x => ‖F (some n) z x - F none z x‖) (f := fun _ => 0) (fun x => 2 * B x)
        (fun n => ((hM (some n) z).sub (hM none z)).norm) (hB.const_mul 2)
        (fun n => ae_of_all _ fun x => by
          rw [Real.norm_eq_abs, abs_norm, two_mul]
          exact (norm_sub_le _ _).trans (add_le_add (hz (some n) x) (hz none x)))
        (ae_of_all _ fun x => by
          simpa only [sub_self, norm_zero] using ((hPt z x).sub (tendsto_const_nhds (x := F none z x))).norm)
      simpa only [R, Pi.sub_apply, integral_zero] using h
    obtain ⟨k, hk⟩ := eventually_atTop.mp (hR.eventually (eventually_lt_nhds (half_pos hε)))
    refine ⟨k, fun n m hn hm s hs => ?_⟩
    have hInt (j : Option ℕ) : Integrable (F j s) μ := hB.mono' (hM j s) (ae_of_all _ fun x => by
      rw [hNorm, hs]; exact hBnd j x)
    have hNormDiff (x : X) : ‖F (some n) s x - F (some m) s x‖ =
        ‖F (some n) z x - F (some m) z x‖ := by
      simp only [F, ← sub_mul, norm_mul, Complex.norm_cpow_eq_rpow_re_of_pos (hδ x), hs, z, Complex.ofReal_re]
    have hTri (x : X) : ‖F (some n) z x - F (some m) z x‖ ≤
        ‖F (some n) z x - F none z x‖ + ‖F (some m) z x - F none z x‖ := by
      simpa only [dist_eq_norm] using dist_triangle_right (F (some n) z x) (F (some m) z x) (F none z x)
    let Mn := ((hzσ (some n)).sub (hzσ none)).norm
    let Mm := ((hzσ (some m)).sub (hzσ none)).norm
    calc
      _ = ‖∫ x, F (some n) s x - F (some m) s x ∂μ‖ := by
        change ‖(∫ x, F (some n) s x ∂μ) - ∫ x, F (some m) s x ∂μ‖ = _
        rw [integral_sub (hInt _) (hInt _)]
      _ ≤ ∫ x, ‖F (some n) s x - F (some m) s x‖ ∂μ := norm_integral_le_integral_norm _
      _ = ∫ x, ‖F (some n) z x - F (some m) z x‖ ∂μ := integral_congr_ae (ae_of_all _ hNormDiff)
      _ ≤ ∫ x, ‖F (some n) z x - F none z x‖ + ‖F (some m) z x - F none z x‖ ∂μ :=
        integral_mono (((hzσ (some n)).sub (hzσ (some m))).norm) (Mn.add Mm) hTri
      _ = R n + R m := integral_add Mn Mm
      _ ≤ ε := by linarith [hk n hn, hk m hm]
  · obtain ⟨B, hB, hBnd⟩ := hdom s.re hs.le
    exact tendsto_integral_of_dominated_convergence B (fun n => hM (some n) s) hB
      (fun n => ae_of_all _ fun x => by rw [hNorm]; exact hBnd (some n) x) (ae_of_all _ (hPt s))

/-- The translated normalized pair can be chosen continuously in the two translations at
each ordinary spectral value. The integrals are over the ordinary quotient and the reflected
product, with their prescribed measures. -/
def ComplexUnequalTranslateContinuityStatement : Prop :=
  ∀ (r t : ℕ) (h : t < r) (ds es : List ComplexCharacterData), ds.length = r + 1 → es.length = t + 1 →
    ∀ (a : ℂˣ) (D : ComplexQuotientMeasureData t),
      (∀ (W : complexWhittakerModel r ds a) (V : complexWhittakerModel t es (-a)),
        HasComplexPairNormalizedGrowth ds es a (complexCentralSign es ^ r)
          (complexUnequalIntegral h D W.val V.val) (complexUnequalDualIntegral h a D W.val V.val)) →
      ∀ (W : complexWhittakerModel r ds a) (V : complexWhittakerModel t es (-a)),
        let P := G (r + 1) × G (t + 1)
        let I (g : P) := complexUnequalIntegral h D (ρ g.1 W.val) (ρ g.2 V.val)
        let Id (g : P) (s : ℂ) := ∫ p, complexUnequalDualKernel h (ρ g.1 W.val) (ρ g.2 V.val) s p
          ∂complexUnequalDualMeasure (r := r) a D
        ∃ (N Nd : P → ℂ → ℂ),
          (∀ g, Differentiable ℂ (N g) ∧ Differentiable ℂ (Nd g) ∧ HasStripExponentialGrowth (N g) ∧
            HasStripExponentialGrowth (Nd g) ∧
            (∃ σ : ℝ, ∀ s : ℂ, σ < s.re →
              N g s = (complexPairLFactor ds es).denominator s * I g s ∧
              Nd g s = (complexPairLFactor (ds.map ComplexCharacterData.inv)
                (es.map ComplexCharacterData.inv)).denominator s * Id g s) ∧
            ∀ s, Nd g (1 - s) = complexCentralSign es ^ r *
              (complexPairEpsilon ds es a ‖(a : ℂ)‖₊ (nnnorm_pos.mpr a.ne_zero) s : ℂ) * N g s) ∧
          ∀ s, Continuous (fun g => N g s)

set_option maxHeartbeats 2100000 in
theorem complexUnequalTranslateContinuity : ComplexUnequalTranslateContinuityStatement := by
  intro r t h ds es hds hes a D hGrowth W V P I Id
  choose N Nd hN hNd hS hSd hR hE using fun g : P =>
    complexUnequalTranslateGrowth r t h ds es hds hes a D hGrowth W V g.1 g.2
  refine ⟨N, Nd, fun g => ⟨hN g, hNd g, hS g, hSd g, hR g, hE g⟩, fun s => ?_⟩
  apply continuous_iff_seqContinuous.mpr
  intro seq g hg
  let T := insert g.1 (range fun n => (seq n).1)
  let U := insert g.2 (range fun n => (seq n).2)
  have hg₁ : Tendsto (fun n => (seq n).1) atTop (𝓝 g.1) := (continuous_fst.tendsto g).comp hg
  have hg₂ : Tendsto (fun n => (seq n).2) atTop (𝓝 g.2) := (continuous_snd.tendsto g).comp hg
  have hT : IsCompact T := hg₁.isCompact_insert_range
  have hU : IsCompact U := hg₂.isCompact_insert_range
  let p : Option ℕ → P := fun n => n.elim g seq
  have hp (n : Option ℕ) : (p n).1 ∈ T ∧ (p n).2 ∈ U := by
    cases n
    · exact ⟨mem_insert _ _, mem_insert _ _⟩
    · exact ⟨mem_insert_of_mem _ (mem_range_self _), mem_insert_of_mem _ (mem_range_self _)⟩
  let A (j : Option ℕ) := ρ (p j).1 W.val
  let C (j : Option ℕ) := ρ (p j).2 V.val
  let K (j : Option ℕ) := complexUnequalIntegrand h (A j) (C j)
  let Kd (j : Option ℕ) := complexUnequalDualKernel h (A j) (C j)
  let X := Q t × Matrix (Fin (r - (t + 1))) (Fin (t + 1)) ℂ
  let δ := quotientDetAbs (t := t)
  let δd (x : X) := δ x.1
  let μ := D.measure
  let ν := complexUnequalDualMeasure (r := r) a D
  obtain ⟨b, hB, hBd⟩ := translatedUnequalDomination h a D W V T U hT hU
  have hK (j : Option ℕ) (z : ℂ) (x : Q t) : K j z x = K j 0 x * (δ x : ℂ) ^ z :=
    complexUnequalIntegrand_eq_mul h (A j) (C j) z x
  have hKd (j : Option ℕ) (z : ℂ) (x : X) : Kd j z x = Kd j 0 x * (δd x : ℂ) ^ z :=
    complexUnequalDualKernel_eq_mul h (A j) (C j) z x
  have hWc : Continuous W.val := (contMDiff_of_mem_complexWhittakerModel W.2).continuous
  have hVc : Continuous V.val := (contMDiff_of_mem_complexWhittakerModel V.2).continuous
  have hAc (j : Option ℕ) : Continuous (A j) := hWc.comp (continuous_id.mul_const _)
  have hCc (j : Option ℕ) : Continuous (C j) := hVc.comp (continuous_id.mul_const _)
  have hA (j : Option ℕ) := hasLeftCharacter_of_rightTranslate W (p j).1
  have hC (j : Option ℕ) := hasLeftCharacter_of_rightTranslate V (p j).2
  have hMK (j : Option ℕ) (z : ℂ) : AEStronglyMeasurable (fun x => K j 0 x * (δ x : ℂ) ^ z) μ := by
    simp_rw [← hK]
    exact (continuous_ordinaryKernel h (hA j) (hC j) (hAc j) (hCc j) z).aestronglyMeasurable
  have hMKd (j : Option ℕ) (z : ℂ) : AEStronglyMeasurable (fun x => Kd j 0 x * (δd x : ℂ) ^ z) ν := by
    simp_rw [← hKd]
    exact (continuous_dualKernel h (hA j) (hC j) (hAc j) (hCc j) z).aestronglyMeasurable
  have hNorm (j : Option ℕ) (x : Q t) (u : ℝ) : ‖K j (u : ℂ) x‖ = ‖K j 0 x‖ * δ x ^ u :=
    ArchimedeanRealPairIdentity.norm_kernel (K := K j) quotientDetAbs_pos (hK j) u x
  have hNormd (j : Option ℕ) (x : X) (u : ℝ) : ‖Kd j (u : ℂ) x‖ = ‖Kd j 0 x‖ * δd x ^ u :=
    ArchimedeanRealPairIdentity.norm_kernel (K := Kd j) (δ := δd) (fun x => quotientDetAbs_pos x.1) (hKd j) u x
  have hbnd (u : ℝ) (hu : b + 1 ≤ u) : ∃ B : Q t → ℝ, Integrable B μ ∧ ∀ j x, ‖K j 0 x‖ * δ x ^ u ≤ B x := by
    obtain ⟨B, hBi, hB'⟩ := hB u
    refine ⟨B, hBi, fun j x => ?_⟩
    exact (hNorm j x u) ▸ hB' ((p j).1, (p j).2, (u : ℂ))
      ⟨(hp j).1, (hp j).2, mem_univ _⟩ (by simp; linarith) (by simp) x
  have hbndd (u : ℝ) (hu : b + 1 ≤ u) : ∃ B : X → ℝ, Integrable B ν ∧ ∀ j x, ‖Kd j 0 x‖ * δd x ^ u ≤ B x := by
    obtain ⟨B, hBi, hB'⟩ := hBd u
    refine ⟨B, hBi, fun j x => ?_⟩
    exact (hNormd j x u) ▸ hB' ((p j).1, (p j).2, (u : ℂ))
      ⟨(hp j).1, (hp j).2, mem_univ _⟩ (by simp; linarith) (by simp) x
  have hLA (x : G (r + 1)) : Tendsto (fun n => A (some n) x) atTop (𝓝 (A none x)) :=
    ((hWc.comp (continuous_const.mul continuous_id)).tendsto _).comp hg₁
  have hLC (x : G (t + 1)) : Tendsto (fun n => C (some n) x) atTop (𝓝 (C none x)) :=
    ((hVc.comp (continuous_const.mul continuous_id)).tendsto _).comp hg₂
  have hLK (x : Q t) : Tendsto (fun n => K (some n) 0 x) atTop (𝓝 (K none 0 x)) := by
    unfold K complexUnequalIntegrand ArchimedeanLocal.unequalIntegrand
    exact ((hLA _).mul (hLC _)).mul tendsto_const_nhds
  have hLKd (x : X) : Tendsto (fun n => Kd (some n) 0 x) atTop (𝓝 (Kd none 0 x)) := by
    unfold Kd complexUnequalDualKernel ArchimedeanLocal.blockKernel ArchimedeanLocal.dualFunction
    exact ((hLA _).mul (hLC _)).mul tendsto_const_nhds
  have hEo (j : Option ℕ) (z : ℂ) : (∫ x, K j 0 x * (δ x : ℂ) ^ z ∂μ) = I (p j) z :=
    integral_congr_ae (ae_of_all _ fun x => (hK j z x).symm)
  have hEd (j : Option ℕ) (z : ℂ) : (∫ x, Kd j 0 x * (δd x : ℂ) ^ z ∂ν) = Id (p j) z :=
    integral_congr_ae (ae_of_all _ fun x => (hKd j z x).symm)
  obtain ⟨hD, hCI, hLim⟩ := mellin_sequence μ (fun j => K j 0) δ quotientDetAbs_pos (b + 1) hMK hbnd hLK
  obtain ⟨hDd, hCId, _⟩ := mellin_sequence ν (fun j => Kd j 0) δd (fun x => quotientDetAbs_pos x.1)
    (b + 1) hMKd hbndd hLKd
  simp only [hEo] at hD hCI hLim
  simp only [hEd] at hDd hCId
  have hsign : complexCentralSign es ^ r ≠ 0 := pow_ne_zero _ (fun hz => by
    have hh := complexCentralSign_sq es
    rw [hz, zero_pow (by decide : 2 ≠ 0)] at hh
    exact zero_ne_one hh)
  obtain ⟨M, M₀, hM, hMR, hML, hM₀, _, hM₀R⟩ := complexPairNormalizedApproximation ds es a _ hsign (b + 1)
    (fun j => I (p (some j))) (fun j => Id (p (some j))) (I (p none))
    (fun j => ⟨N _, Nd _, hN _, hNd _, hS _, hSd _, hR _, hE _⟩)
    (fun j => hD (some j)) (fun j => hDd (some j)) hCI hCId hLim
  have hUnique (F : ℂ → ℂ) (hd : Differentiable ℂ F) (k : P)
      (hf : ∀ z : ℂ, b + 1 < z.re → F z = (complexPairLFactor ds es).denominator z * I k z) :
      F = N k := by
    obtain ⟨c, hc⟩ := hR k
    let z₀ : ℂ := (((max c (b + 1) + 1 : ℝ)) : ℂ)
    have hz₀ : max c (b + 1) < z₀.re := by simp [z₀]
    apply AnalyticOnNhd.eq_of_eventuallyEq (fun z _ => hd.analyticAt z) (fun z _ => (hN k).analyticAt z) (z₀ := z₀)
    filter_upwards [(isOpen_lt continuous_const Complex.continuous_re).mem_nhds hz₀] with z hz
    exact (hf z ((le_max_right _ _).trans_lt hz)).trans ((hc z ((le_max_left _ _).trans_lt hz)).1.symm)
  have hEq (n : ℕ) : M n = N (seq n) := hUnique (M n) (hM n) (seq n) (hMR n)
  have hEq₀ : M₀ = N g := hUnique M₀ hM₀ g hM₀R
  have ht := hML.tendstoLocallyUniformlyOn.tendsto_at (mem_univ s)
  change Tendsto (fun n => N (seq n) s) atTop (𝓝 (N g s))
  simpa only [hEq, hEq₀, Function.comp_apply] using ht

end Langlands.Global.RankinSelbergGlobal.ComplexUnequalWeightedTranslation
