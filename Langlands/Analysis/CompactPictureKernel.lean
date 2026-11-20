import Mathlib.MeasureTheory.Function.LocallyIntegrable
import Mathlib.MeasureTheory.Group.Integral
import Mathlib.MeasureTheory.Integral.Bochner.ContinuousLinearMap
import Mathlib.MeasureTheory.Integral.Prod

/-! # The integral kernel of an integrated action in a compact picture -/

noncomputable section

open MeasureTheory
open scoped Pointwise

set_option autoImplicit false

namespace Langlands.Analysis

variable {G K X : Type*}
  [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
  [Group K] [TopologicalSpace K] [IsTopologicalGroup K] [CompactSpace K]
  [TopologicalSpace X] [CompactSpace X]
  (i : K →* G) (hi : Continuous i) (p : C(X, G)) (q : C(G, K)) (c f : C(G, ℂ))

omit [IsTopologicalGroup G] [TopologicalSpace K] [IsTopologicalGroup K]
  [CompactSpace K] [CompactSpace X] in
private theorem mem_compactKernelSupport (x : X) (g : G) (z : K)
    (hg : f ((p x)⁻¹ * g * i z) ≠ 0) :
    g ∈ Set.range p * tsupport f * Set.range i := by
  have h : p x * ((p x)⁻¹ * g * i z) * i z⁻¹ = g := by
    rw [map_inv]
    group
  rw [← h]
  exact Set.mul_mem_mul
    (Set.mul_mem_mul ⟨x, rfl⟩ (subset_tsupport f hg)) ⟨z⁻¹, rfl⟩

include hi in
omit [IsTopologicalGroup K] in
private theorem isCompact_compactKernelSupport (hf : HasCompactSupport f) :
    IsCompact (Set.range p * tsupport f * Set.range i) :=
  ((isCompact_range p.continuous).mul hf).mul (isCompact_range hi)

private def compactKernelIntegrand (g : G) : C(X × K, ℂ) :=
  ⟨fun xz => c g * f ((p xz.1)⁻¹ * g * i ((q g)⁻¹ * xz.2)), by
    apply continuous_const.mul
    exact f.continuous.comp (((p.continuous.comp continuous_fst).inv.mul continuous_const).mul
      (hi.comp (continuous_const.mul continuous_snd)))⟩

omit [CompactSpace K] [CompactSpace X] in
private theorem continuous_compactKernelIntegrand :
    Continuous (compactKernelIntegrand i hi p q c f) := by
  apply ContinuousMap.continuous_of_continuous_uncurry
  change Continuous (fun p' : G × (X × K) =>
    c p'.1 * f ((p p'.2.1)⁻¹ * p'.1 * i ((q p'.1)⁻¹ * p'.2.2)))
  exact (c.continuous.comp continuous_fst).mul (f.continuous.comp
    (((p.continuous.comp (continuous_fst.comp continuous_snd)).inv.mul continuous_fst).mul
      (hi.comp ((q.continuous.comp continuous_fst).inv.mul (continuous_snd.comp continuous_snd)))))

private theorem hasCompactSupport_compactKernelIntegrand (hf : HasCompactSupport f) :
    HasCompactSupport (compactKernelIntegrand i hi p q c f) := by
  apply HasCompactSupport.intro (isCompact_compactKernelSupport i hi p f hf)
  intro g hg
  ext xz
  change c g * f ((p xz.1)⁻¹ * g * i ((q g)⁻¹ * xz.2)) = 0
  have hzero : f ((p xz.1)⁻¹ * g * i ((q g)⁻¹ * xz.2)) = 0 :=
    not_not.mp (fun h => hg (mem_compactKernelSupport i p f xz.1 g _ h))
  rw [hzero, mul_zero]

variable [MeasurableSpace G] [BorelSpace G] (μ : Measure G) [IsFiniteMeasureOnCompacts μ]

/-- The continuous kernel obtained by averaging the scalar test against the compact factor. -/
def compactPictureKernel : C(X × K, ℂ) :=
  ∫ g, compactKernelIntegrand i hi p q c f g ∂μ

/-- The pointwise integral expression for the compact-picture kernel. -/
theorem compactPictureKernel_apply (hf : HasCompactSupport f) (x : X) (z : K) :
    compactPictureKernel i hi p q c f μ (x, z) =
      ∫ g, c g * f ((p x)⁻¹ * g * i ((q g)⁻¹ * z)) ∂μ := by
  have h := (continuous_compactKernelIntegrand i hi p q c f).integrable_of_hasCompactSupport
    (hasCompactSupport_compactKernelIntegrand i hi p q c f hf) (μ := μ)
  exact ContinuousMap.integral_apply h (x, z)

variable [SecondCountableTopology K]
  [MeasurableSpace K] [BorelSpace K] [SFinite μ] [μ.IsMulRightInvariant]
  (ν : Measure K) [IsProbabilityMeasure ν] [ν.IsMulLeftInvariant]

/-- Right averaging converts integration of an extended compact profile into the continuous
kernel on the compact parameters. The extension uses the prescribed compact factor and weight. -/
theorem integral_compactPictureKernel (hf : HasCompactSupport f)
    (hq : ∀ (g : G) (r : K), q (g * i r) = q g * r)
    (hc : ∀ (g : G) (r : K), c (g * i r) = c g)
    (u : C(K, ℂ)) (x : X) :
    (∫ g, f ((p x)⁻¹ * g) * (c g * u (q g)) ∂μ) =
      ∫ z, compactPictureKernel i hi p q c f μ (x, z) * u z ∂ν := by
  let A : G × K → ℂ := fun gr =>
    c gr.1 * f ((p x)⁻¹ * gr.1 * i gr.2) * u (q gr.1 * gr.2)
  let B : G × K → ℂ := fun gz =>
    c gz.1 * f ((p x)⁻¹ * gz.1 * i ((q gz.1)⁻¹ * gz.2)) * u gz.2
  let S := Set.range p * tsupport f * Set.range i
  have hS : IsCompact (S ×ˢ (Set.univ : Set K)) :=
    (isCompact_compactKernelSupport i hi p f hf).prod isCompact_univ
  have hAcont : Continuous A := ((c.continuous.comp continuous_fst).mul
    (f.continuous.comp ((continuous_const.mul continuous_fst).mul (hi.comp continuous_snd)))).mul
      (u.continuous.comp ((q.continuous.comp continuous_fst).mul continuous_snd))
  have hBcont : Continuous B := ((c.continuous.comp continuous_fst).mul
    (f.continuous.comp ((continuous_const.mul continuous_fst).mul
      (hi.comp ((q.continuous.comp continuous_fst).inv.mul continuous_snd))))).mul
        (u.continuous.comp continuous_snd)
  have hA : Integrable A (μ.prod ν) := hAcont.integrable_of_hasCompactSupport
    (HasCompactSupport.intro hS (fun gr hg => by
      change c gr.1 * f ((p x)⁻¹ * gr.1 * i gr.2) * u (q gr.1 * gr.2) = 0
      have hz : f ((p x)⁻¹ * gr.1 * i gr.2) = 0 := not_not.mp (fun hn =>
        hg ⟨mem_compactKernelSupport i p f x gr.1 gr.2 hn, Set.mem_univ _⟩)
      rw [hz, mul_zero, zero_mul]))
  have hB : Integrable B (μ.prod ν) := hBcont.integrable_of_hasCompactSupport
    (HasCompactSupport.intro hS (fun gz hg => by
      change c gz.1 * f ((p x)⁻¹ * gz.1 * i ((q gz.1)⁻¹ * gz.2)) * u gz.2 = 0
      have hz : f ((p x)⁻¹ * gz.1 * i ((q gz.1)⁻¹ * gz.2)) = 0 := not_not.mp (fun hn =>
        hg ⟨mem_compactKernelSupport i p f x gz.1 _ hn, Set.mem_univ _⟩)
      rw [hz, mul_zero, zero_mul]))
  have hright (r : K) : (∫ g, A (g, r) ∂μ) = ∫ g, f ((p x)⁻¹ * g) * (c g * u (q g)) ∂μ := by
    have hr := integral_mul_right_eq_self (μ := μ)
      (fun g => f ((p x)⁻¹ * g) * (c g * u (q g))) (i r)
    simpa only [A, hc, hq, mul_assoc, mul_left_comm] using hr
  have hleft (g : G) : (∫ r, A (g, r) ∂ν) = ∫ z, B (g, z) ∂ν := by
    have hl := integral_mul_left_eq_self (μ := ν) (fun z => B (g, z)) (q g)
    simpa only [A, B, ← mul_assoc, inv_mul_cancel, one_mul] using hl
  calc
    _ = ∫ r, (∫ g, A (g, r) ∂μ) ∂ν := by simp [hright]
    _ = ∫ g, (∫ r, A (g, r) ∂ν) ∂μ := (integral_integral_swap hA).symm
    _ = ∫ g, (∫ z, B (g, z) ∂ν) ∂μ := by simp only [hleft]
    _ = ∫ z, (∫ g, B (g, z) ∂μ) ∂ν := integral_integral_swap hB
    _ = _ := by simp only [B, integral_mul_const, compactPictureKernel_apply i hi p q c f μ hf]

end Langlands.Analysis
