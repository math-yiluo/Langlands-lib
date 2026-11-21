import Langlands.Analysis.SliceNormalPrimitive
import Langlands.Analysis.SliceSupportedDistribution

/-! # A transverse derivative forces a slice-supported distribution to vanish -/

noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set Metric Filter TopologicalSpace
open scoped ContDiff Distributions Topology

namespace Langlands.Analysis

universe uX uY uV uI

variable {X : Type uX} [NormedAddCommGroup X] [NormedSpace ℝ X]
  {Y : Type uY} [NormedAddCommGroup Y] [NormedSpace ℝ Y]
  {V : Type uV} [NormedAddCommGroup V] [NormedSpace ℝ V]

/-- A compact support with a closed interval in the last coordinate,
written in coordinates that retain the flat slice `X × {0}`. -/
def normalCoordinateBox (K₀ : Compacts (X × Y)) (R : ℝ) : Compacts (X × Y × ℝ) :=
  ⟨(fun p : (X × Y) × ℝ => (p.1.1, p.1.2, p.2)) '' ((K₀ : Set (X × Y)) ×ˢ closedBall 0 R),
    (K₀.isCompact.prod (isCompact_closedBall (0 : ℝ) R)).image
      (continuous_fst.fst.prodMk (continuous_fst.snd.prodMk continuous_snd))⟩

omit [NormedSpace ℝ X] [NormedSpace ℝ Y] in
theorem mem_normalCoordinateBox {K₀ : Compacts (X × Y)} {R : ℝ} {p : X × Y × ℝ} :
    p ∈ (normalCoordinateBox K₀ R : Set (X × Y × ℝ)) ↔
      (p.1, p.2.1) ∈ (K₀ : Set (X × Y)) ∧ p.2.2 ∈ closedBall 0 R := by
  constructor
  · rintro ⟨q, hq, rfl⟩
    exact hq
  · intro hp
    exact ⟨((p.1, p.2.1), p.2.2), hp, rfl⟩

/-- Constant directional differentiation in the space of tests with
a fixed compact support. -/
def compactTestLineDeriv {K : Compacts X} (v : X) : 𝓓_{K}(X, ℝ) →L[ℝ] 𝓓_{K}(X, ℝ) :=
  (ContDiffMapSupportedIn.postcompCLM (ContinuousLinearMap.apply ℝ ℝ v)).comp
    (ContDiffMapSupportedIn.fderivCLM ℝ ⊤ ⊤)

@[simp]
theorem compactTestLineDeriv_apply {K : Compacts X} (v : X) (f : 𝓓_{K}(X, ℝ)) (p : X) :
    compactTestLineDeriv v f p = fderiv ℝ f p v := by
  change (ContDiffMapSupportedIn.fderivCLM ℝ ⊤ ⊤ f p) v = _
  rw [ContDiffMapSupportedIn.fderivCLM_apply_of_le ℝ f (by simp)]

/-- A normal primitive cut off inside the same rectangular support.
The transverse derivative agrees with the original test near the zero slice. -/
theorem exists_compactTest_normalPrimitive (K₀ : Compacts (X × Y)) {R : ℝ} (hR : 0 < R)
    (f : 𝓓_{normalCoordinateBox K₀ R}(X × Y × ℝ, ℝ))
    (m : ℕ) (hf : ∀ x : X, ∀ j < m, iteratedFDeriv ℝ j f (x, (0, 0)) = 0) :
    ∃ g : 𝓓_{normalCoordinateBox K₀ R}(X × Y × ℝ, ℝ),
      IsFlatOnZeroSlice m (g : X × Y × ℝ → ℝ) ∧
        tsupport (f - compactTestLineDeriv (0, 0, 1) g) ⊆
          {p : X × Y × ℝ | p.2 ≠ 0} := by
  let b : ContDiffBump (0 : ℝ) := ⟨R / 2, R, half_pos hR, half_lt_self hR⟩
  let h : X × Y × ℝ → ℝ := sliceNormalPrimitive f
  have hh : ContDiff ℝ ∞ h := contDiff_sliceNormalPrimitive f.contDiff
  have hb : ContDiff ℝ ∞ (fun p : X × Y × ℝ => b p.2.2) :=
    b.contDiff.comp contDiff_snd.snd
  let g : 𝓓_{normalCoordinateBox K₀ R}(X × Y × ℝ, ℝ) :=
    ⟨fun p => b p.2.2 • h p, hb.smul hh, fun p hp => by
      change b p.2.2 • h p = 0
      by_cases h₀ : (p.1, p.2.1) ∈ (K₀ : Set (X × Y))
      · have ht : R ≤ dist p.2.2 0 := by
          by_contra! ht
          exact hp (mem_normalCoordinateBox.mpr ⟨h₀, mem_closedBall.mpr ht.le⟩)
        rw [b.zero_of_le_dist ht, zero_smul]
      · have hf₀ (t : ℝ) : f (p.1, p.2.1, t) = 0 :=
          f.zero_on_compl (fun ht => h₀ (mem_normalCoordinateBox.mp ht).1)
        change b p.2.2 • (∫ t in 0..p.2.2, f (p.1, p.2.1, t)) = 0
        simp only [hf₀, intervalIntegral.integral_zero, smul_zero]⟩
  refine ⟨g, (isFlatOnZeroSlice_sliceNormalPrimitive f.contDiff m hf).smul hh hb, ?_⟩
  have hclosed : IsClosed {p : X × Y × ℝ | R / 2 ≤ ‖p.2.2‖} :=
    isClosed_le continuous_const continuous_snd.snd.norm
  refine (closure_minimal ?_ hclosed).trans ?_
  · intro p hp
    by_contra! hp'
    change ¬ R / 2 ≤ ‖p.2.2‖ at hp'
    have hne : (g : X × Y × ℝ → ℝ) =ᶠ[𝓝 p] h := by
      have hball : p.2.2 ∈ ball (0 : ℝ) (R / 2) :=
        mem_ball.mpr (by rwa [dist_zero_right, ← not_le])
      filter_upwards [continuous_snd.snd.continuousAt (isOpen_ball.mem_nhds hball)] with q hq
      change b q.2.2 • h q = h q
      rw [b.one_of_mem_closedBall (ball_subset_closedBall hq), one_smul]
    apply hp
    change f p - compactTestLineDeriv (0, 0, 1) g p = 0
    rw [compactTestLineDeriv_apply, hne.fderiv_eq, fderiv_sliceNormalPrimitive_last f.contDiff,
      sub_self]
  · intro p hp hz
    change R / 2 ≤ ‖p.2.2‖ at hp
    rw [hz, Prod.snd_zero, norm_zero] at hp
    exact (not_le_of_gt (half_pos hR)) hp

/-- A classical distribution supported on the flat slice vanishes on a
fixed rectangular support when its transverse derivative equation is
a finite sum of operations preserving the vanishing order of jets. -/
theorem distribution_eq_zero_on_box_of_transverse_equation [FiniteDimensional ℝ Y]
    {Ω : Opens (X × Y × ℝ)} (T : 𝓓'(Ω, V))
    (hT : Distribution.IsVanishingOn T {p : X × Y × ℝ | p.2 ≠ 0})
    (K₀ : Compacts (X × Y)) {R : ℝ} (hR : 0 < R)
    (hK : (normalCoordinateBox K₀ R : Set (X × Y × ℝ)) ⊆ Ω)
    {ι : Type uI} [Fintype ι]
    (D : ι → 𝓓_{normalCoordinateBox K₀ R}(X × Y × ℝ, ℝ) →ₗ[ℝ]
      𝓓_{normalCoordinateBox K₀ R}(X × Y × ℝ, ℝ)) (B : ι → V →L[ℝ] V)
    (hD : ∀ i m (f : 𝓓_{normalCoordinateBox K₀ R}(X × Y × ℝ, ℝ)),
      IsFlatOnZeroSlice m (f : X × Y × ℝ → ℝ) →
        IsFlatOnZeroSlice m (D i f : X × Y × ℝ → ℝ))
    (he : ∀ f, T (TestFunction.ofSupportedIn hK (compactTestLineDeriv (0, 0, 1) f)) =
      ∑ i, B i (T (TestFunction.ofSupportedIn hK (D i f)))) :
    ∀ f : 𝓓_{normalCoordinateBox K₀ R}(X × Y × ℝ, ℝ),
      T (TestFunction.ofSupportedIn hK f) = 0 := by
  let K := normalCoordinateBox K₀ R
  let L : 𝓓_{K}(X × Y × ℝ, ℝ) →L[ℝ] V :=
    (show 𝓓(Ω, ℝ) →L[ℝ] V from T).comp (TestFunction.ofSupportedInCLM ℝ hK)
  obtain ⟨n, hn⟩ := exists_order_annihilate_flat_on_slice T hT K hK
  have descend (m : ℕ) (hm : ∀ f : 𝓓_{K}(X × Y × ℝ, ℝ),
      IsFlatOnZeroSlice m (f : X × Y × ℝ → ℝ) → L f = 0) :
      ∀ f : 𝓓_{K}(X × Y × ℝ, ℝ),
        (∀ x : X, ∀ j < m, iteratedFDeriv ℝ j f (x, (0, 0)) = 0) → L f = 0 := by
    intro f hf
    obtain ⟨g, hg, hsupport⟩ := exists_compactTest_normalPrimitive K₀ hR f m hf
    have hs : L (f - compactTestLineDeriv (0, 0, 1) g) = 0 :=
      hT (TestFunction.ofSupportedIn hK _) hsupport
    rw [map_sub, sub_eq_zero] at hs
    rw [hs]
    change T (TestFunction.ofSupportedIn hK (compactTestLineDeriv (0, 0, 1) g)) = _
    rw [he]
    exact Finset.sum_eq_zero (fun i _ => by
      change B i (L (D i g)) = _
      rw [hm (D i g) (hD i m g hg), map_zero])
  change ∀ f, L f = 0
  have hstart : ∀ f : 𝓓_{K}(X × Y × ℝ, ℝ), IsFlatOnZeroSlice n (f : X × Y × ℝ → ℝ) →
      L f = 0 := hn
  clear hn
  induction n with
  | zero => exact fun f => descend 0 hstart f (fun _ _ hj => (Nat.not_lt_zero _ hj).elim)
  | succ n ih => exact ih (fun f hf => descend (n + 1) hstart f (fun x j hj => hf x j (by omega)))

end Langlands.Analysis
