import Langlands.HarmonicAnalysis.Distribution.SmoothTestIntegral
import Mathlib.Analysis.Calculus.BumpFunction.FiniteDimension
import Mathlib.MeasureTheory.Group.Integral

/-! # Right invariant smooth distributions in global group coordinates -/

noncomputable section

open Set TopologicalSpace MeasureTheory
open scoped Classical ContDiff Distributions

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

namespace Langlands.HarmonicAnalysis

universe u v

/-- Complex smooth tests on a full real normed space. -/
private abbrev FullTest (E : Type v) [NormedAddCommGroup E] [NormedSpace ℝ E] :=
  𝓓((⊤ : Opens E), ℂ)

/-- In smooth global coordinates, a right invariant test distribution is a scalar
multiple of integration against a bi-invariant Haar measure. -/
def SmoothRightInvariantHaarStatement : Prop :=
  ∀ {G : Type u} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
    [MeasurableSpace G] [BorelSpace G] [MeasurableMul G]
    {E : Type v} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    [MeasurableSpace E] [BorelSpace E]
    (e : G ≃ₜ E) (μ : Measure G) [μ.IsHaarMeasure] [μ.IsMulRightInvariant],
    ContDiff ℝ ∞ (fun p : E × E => e (e.symm p.1 * e.symm p.2)) →
    ContDiff ℝ ∞ (fun x : E => e (e.symm x)⁻¹) →
    ∀ T : FullTest E →L[ℂ] ℂ,
      (∀ (a : G) (f f' : FullTest E),
        (∀ x : E, f' x = f (e (e.symm x * a))) → T f' = T f) →
      ∃ c : ℂ, ∀ f : FullTest E, T f = c * (∫ x, f x ∂(μ.map e))

set_option maxHeartbeats 1400000 in
theorem smoothRightInvariantHaar : SmoothRightInvariantHaarStatement.{u, v} := by
  intro G _ _ _ _ _ _ E _ _ _ _ _ e μ _ _ hm hi T hT
  let ν := μ.map e
  let : IsFiniteMeasureOnCompacts ν := Measure.IsFiniteMeasureOnCompacts.map μ e
  let : ν.IsOpenPosMeasure := e.continuous.isOpenPosMeasure_map e.surjective
  let m (x y : E) := e (e.symm x * e.symm y)
  let i (x : E) := e (e.symm x)⁻¹
  have hm' : ContDiff ℝ ∞ (fun p : E × E => m p.1 p.2) := hm
  have hi' : ContDiff ℝ ∞ i := hi
  have hRight (f : E → ℂ) (z : E) : (∫ y, f (m y z) ∂ν) = ∫ y, f y ∂ν := by
    simp only [ν, e.measurableEmbedding.integral_map, m, e.symm_apply_apply]
    exact integral_mul_right_eq_self (μ := μ) (f ∘ e) (e.symm z)
  have hLeft (f : E → ℂ) (z : E) : (∫ y, f (m z y) ∂ν) = ∫ y, f y ∂ν := by
    simp only [ν, e.measurableEmbedding.integral_map, m, e.symm_apply_apply]
    exact integral_mul_left_eq_self (μ := μ) (f ∘ e) (e.symm z)
  let b : ContDiffBump (0 : E) := ⟨1, 2, zero_lt_one, one_lt_two⟩
  let bC (x : E) : ℂ := (b x : ℂ)
  let Kb : Compacts E := ⟨tsupport b, b.hasCompactSupport⟩
  have hB (x : E) (hx : x ∉ Kb) : bC x = 0 := by
    simp only [bC, image_eq_zero_of_notMem_tsupport hx, Complex.ofReal_zero]
  let g : FullTest E := TestFunction.ofSupportedIn (subset_univ (Kb : Set E))
    (⟨bC, Complex.ofRealCLM.contDiff.comp b.contDiff, hB⟩ : 𝓓_{Kb}(E, ℂ))
  have hg : (∫ x, g x ∂ν) ≠ 0 := by
    change (∫ x, (b x : ℂ) ∂ν) ≠ 0
    rw [integral_complex_ofReal]
    exact Complex.ofReal_ne_zero.mpr (ne_of_gt (b.continuous.integral_pos_of_hasCompactSupport_nonneg_nonzero
      (x := (0 : E)) b.hasCompactSupport (fun _ => b.nonneg)
      (by rw [b.one_of_mem_closedBall (Metric.mem_closedBall_self zero_le_one)]; norm_num)))
  let Kg : Compacts E := ⟨tsupport g, g.hasCompactSupport⟩
  let Ki : Compacts E := ⟨i '' (Kg : Set E), Kg.isCompact.image hi'.continuous⟩
  have hii (x : E) : i (i x) = x := by simp [i]
  have hgi (x : E) (hx : x ∉ Ki) : g (i x) = 0 := by
    apply image_eq_zero_of_notMem_tsupport
    exact fun hs => hx ⟨i x, hs, hii x⟩
  let gi : FullTest E := TestFunction.ofSupportedIn (subset_univ (Ki : Set E))
    (⟨fun x => g (i x), g.contDiff.comp hi', hgi⟩ : 𝓓_{Ki}(E, ℂ))
  refine ⟨T gi / (∫ x, g x ∂ν), fun f => ?_⟩
  let Kf : Compacts E := ⟨tsupport f, f.hasCompactSupport⟩
  let Q : Compacts E := ⟨(fun p : E × E => m p.1 p.2) '' ((Kg : Set E) ×ˢ (Kf : Set E)),
    (Kg.isCompact.prod Kf.isCompact).image hm'.continuous⟩
  let H (p : E × E) := f p.2 * g (m p.1 (i p.2))
  let H' (p : E × E) := f (m p.2 p.1) * g (i p.2)
  have hH : ContDiff ℝ ∞ H := (f.contDiff.comp contDiff_snd).mul
    (g.contDiff.comp (hm'.comp (contDiff_fst.prodMk (hi'.comp contDiff_snd))))
  have hH' : ContDiff ℝ ∞ H' := (f.contDiff.comp (hm'.comp (contDiff_snd.prodMk contDiff_fst))).mul
    (g.contDiff.comp (hi'.comp contDiff_snd))
  have hs : ∀ y ∈ Q, ∀ x ∉ Kf, H (y, x) = 0 := fun y _ x hx => by
    change f x * g (m y (i x)) = 0
    rw [image_eq_zero_of_notMem_tsupport hx, zero_mul]
  have hs' : ∀ y ∈ Q, ∀ x ∉ Ki, H' (y, x) = 0 := fun y _ x hx => by
    change f (m x y) * g (i x) = 0
    rw [hgi x hx, mul_zero]
  have hQ (x y : E) (hy : y ∉ Q) : H (y, x) = 0 := by
    by_contra hn
    have hf := subset_tsupport f (left_ne_zero_of_mul hn)
    have hg := subset_tsupport g (right_ne_zero_of_mul hn)
    exact hy ⟨(m y (i x), x), ⟨hg, hf⟩, by simp [m, i, mul_assoc]⟩
  have hQ' (x y : E) (hy : y ∉ Q) : H' (y, x) = 0 := by
    by_contra hn
    have hf := subset_tsupport f (left_ne_zero_of_mul hn)
    have hg := subset_tsupport g (right_ne_zero_of_mul hn)
    exact hy ⟨(i x, m x y), ⟨hg, hf⟩, by simp [m, i]⟩
  let νQ : Measure Q := ν.comap Subtype.val
  let : CompactSpace Q := isCompact_iff_compactSpace.mp Q.isCompact
  let : IsFiniteMeasureOnCompacts νQ := IsFiniteMeasureOnCompacts.comap' ν continuous_subtype_val
    (MeasurableEmbedding.subtype_coe Q.isCompact.isClosed.measurableSet)
  let lift (K : Compacts E) : 𝓓_{K}(E, ℂ) →L[ℂ] FullTest E := TestFunction.ofSupportedInCLM ℂ (subset_univ _)
  obtain ⟨F, hF, hFT⟩ := smoothTestIntegral Q Kf νQ H hH hs
  obtain ⟨F', hF', hFT'⟩ := smoothTestIntegral Q Ki νQ H' hH' hs'
  have hEq (t : Q) : T (lift Ki (compactTestFamily hH' hs' t)) = T (lift Kf (compactTestFamily hH hs t)) := by
    apply hT (e.symm t.val)
    intro x
    change H' (t.val, x) = H (t.val, m x t.val)
    simp [H, H', m, i]
  have hAvg : T (lift Kf F) = T (lift Ki F') := by
    have h := hFT (T.comp (lift Kf))
    have h' := hFT' (T.comp (lift Ki))
    simp only [ContinuousLinearMap.comp_apply] at h h'
    rw [h, h']
    exact integral_congr_ae (ae_of_all _ fun t => (hEq t).symm)
  have hIntegral (A : E → ℂ) (hA : ∀ y, y ∉ Q → A y = 0) :
      (∫ t : Q, A t.val ∂νQ) = ∫ y, A y ∂ν := by
    exact (integral_subtype_comap (μ := ν) Q.isCompact.isClosed.measurableSet A).trans
      (setIntegral_eq_integral_of_forall_compl_eq_zero hA)
  have hAvgF : lift Kf F = (∫ y, g y ∂ν) • f := by
    ext x
    change F x = (∫ y, g y ∂ν) * f x
    rw [hF, hIntegral (fun y => H (y, x)) (hQ x)]
    change (∫ y, f x * g (m y (i x)) ∂ν) = _
    rw [integral_const_mul, hRight g (i x), mul_comm]
  have hAvgF' : lift Ki F' = (∫ y, f y ∂ν) • gi := by
    ext x
    change F' x = (∫ y, f y ∂ν) * g (i x)
    rw [hF', hIntegral (fun y => H' (y, x)) (hQ' x)]
    change (∫ y, f (m x y) * g (i x) ∂ν) = _
    rw [integral_mul_const, hLeft f x]
  rw [hAvgF, hAvgF', map_smul, map_smul, smul_eq_mul, smul_eq_mul] at hAvg
  calc
    T f = ((∫ y, g y ∂ν) * T f) / (∫ y, g y ∂ν) := by field_simp
    _ = (T gi / (∫ y, g y ∂ν)) * (∫ y, f y ∂ν) := by rw [hAvg]; ring

end Langlands.HarmonicAnalysis
