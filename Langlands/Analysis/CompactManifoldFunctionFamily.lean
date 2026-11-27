import Langlands.Analysis.CompactParameterSmoothness
import Mathlib.Analysis.Calculus.ContDiff.FiniteDimension
import Mathlib.Geometry.Manifold.ContMDiffMFDeriv
import Mathlib.Geometry.Manifold.ContMDiff.Atlas

/-! # Smooth compact restriction of a manifold family -/

noncomputable section

open Set
open scoped Manifold ContDiff Topology

set_option autoImplicit false

namespace Langlands.Analysis

variable {X : Type*} [TopologicalSpace X] [CompactSpace X]
  {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]
  {W : Type*} [NormedAddCommGroup W] [NormedSpace ℝ W]
  {N : Type*} [TopologicalSpace N] [ChartedSpace W N] [IsManifold 𝓘(ℝ, W) ∞ N]
  {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- The actual partial derivative in the vector parameter is smooth jointly with
the manifold parameter on an open parameter domain. -/
private theorem contMDiffOn_partialFDeriv {s : Set V} (hs : IsOpen s) {h : V × N → E}
    (hh : ContMDiffOn (𝓘(ℝ, V).prod 𝓘(ℝ, W)) 𝓘(ℝ, E) ∞ h (s ×ˢ univ)) :
    ContMDiffOn (𝓘(ℝ, V).prod 𝓘(ℝ, W)) 𝓘(ℝ, V →L[ℝ] E) ∞
      (fun p : V × N => fderiv ℝ (fun q => h (q, p.2)) p.1) (s ×ˢ univ) := by
  intro p hp
  have hhp : ContMDiffAt (𝓘(ℝ, V).prod 𝓘(ℝ, W)) 𝓘(ℝ, E) ∞ h p :=
    (hh p hp).contMDiffAt ((hs.prod isOpen_univ).mem_nhds hp)
  have hf : ContMDiffAt ((𝓘(ℝ, V).prod 𝓘(ℝ, W)).prod 𝓘(ℝ, V)) 𝓘(ℝ, E) ∞
      (fun q : (V × N) × V => h (q.2, q.1.2)) (p, p.1) :=
    hhp.comp (p, p.1) (contMDiffAt_snd.prodMk (contMDiffAt_snd.comp _ contMDiffAt_fst))
  have hd := hf.mfderiv (m := ∞)
    (fun p : V × N => fun q : V => h (q, p.2)) (fun p : V × N => p.1)
    contMDiffAt_fst (by simp)
  simp only [mfderiv_eq_fderiv] at hd
  erw [inTangentCoordinates_model_space] at hd
  exact hd.contMDiffWithinAt

private theorem hasFDerivAt_of_joint_manifold (j : C(X, N))
    {s : Set V} (hs : IsOpen s) {h : V × N → E}
    (hh : ContMDiffOn (𝓘(ℝ, V).prod 𝓘(ℝ, W)) 𝓘(ℝ, E) ∞ h (s ×ˢ univ))
    {f : V → C(X, E)} (heq : ∀ y ∈ s, ∀ a, f y a = h (y, j a)) {y : V} (hy : y ∈ s) :
    ∃ D : V →L[ℝ] C(X, E), HasFDerivAt f D y ∧
      ∀ v a, D v a = fderiv ℝ (fun p => h (p, j a)) y v := by
  classical
  let d (p : V × N) := fderiv ℝ (fun q => h (q, p.2)) p.1
  have hd : ContMDiffOn (𝓘(ℝ, V).prod 𝓘(ℝ, W)) 𝓘(ℝ, V →L[ℝ] E) ∞ d (s ×ˢ univ) :=
    contMDiffOn_partialFDeriv hs hh
  let D (p : V) : C(X, V →L[ℝ] E) := if hp : p ∈ s then
    ⟨fun a => d (p, j a), hd.continuousOn.comp_continuous (continuous_const.prodMk j.continuous)
      (fun _ => ⟨hp, mem_univ _⟩)⟩ else 0
  have hDeq (p : V) (hp : p ∈ s) (a : X) : D p a = d (p, j a) := by simp [D, hp]
  have hD := continuousOn_compactFamily_of_joint j (fun _ => mem_univ _) hd.continuousOn hDeq
  refine ⟨compactFamilyOperator X V E (D y), hasFDerivAt_compactFamily hs hy hD ?_, fun _ a => ?_⟩
  · intro p hp a
    rw [hDeq p hp]
    have hslice := ((hh (p, j a) ⟨hp, mem_univ _⟩).contMDiffAt
      ((hs.prod isOpen_univ).mem_nhds ⟨hp, mem_univ _⟩)).comp p
      (contMDiffAt_id.prodMk contMDiffAt_const)
    apply (hslice.contDiffAt.differentiableAt (by simp)).hasFDerivAt.congr_of_eventuallyEq
    filter_upwards [hs.mem_nhds hp] with z hz
    exact heq z hz a
  · exact congrArg (fun T : V →L[ℝ] E => T _) (hDeq y hy a)

variable [FiniteDimensional ℝ V]

private theorem contDiffOn_nat_of_joint_manifold (j : C(X, N))
    {s : Set V} (hs : IsOpen s) (m : ℕ) : ∀ {h : V × N → E},
    ContMDiffOn (𝓘(ℝ, V).prod 𝓘(ℝ, W)) 𝓘(ℝ, E) ∞ h (s ×ˢ univ) →
      ∀ {f : V → C(X, E)}, (∀ y ∈ s, ∀ a, f y a = h (y, j a)) → ContDiffOn ℝ m f s := by
  induction m with
  | zero =>
    intro h hh f heq
    exact contDiffOn_zero.mpr (continuousOn_compactFamily_of_joint j (fun _ => mem_univ _)
      hh.continuousOn heq)
  | succ m ih =>
    intro h hh f heq
    have hD (p : V) (hp : p ∈ s) := hasFDerivAt_of_joint_manifold j hs hh heq hp
    rw [Nat.cast_succ]
    refine contDiffOn_succ_of_fderiv_apply (fun p hp => ?_) (by simp) fun v => ?_
    · obtain ⟨D, hD, _⟩ := hD p hp
      exact hD.differentiableAt.differentiableWithinAt
    · apply ih ((contMDiffOn_partialFDeriv hs hh).clm_apply
        (contMDiffOn_const (c := v)))
      intro p hp a
      obtain ⟨D, hD, hDeq⟩ := hD p hp
      rw [fderivWithin_of_isOpen hs hp, hD.fderiv]
      exact hDeq v a

/-- Restricting the second variable of a jointly smooth map to a continuous compact family
produces a smooth map into continuous functions with their supremum norm. -/
theorem contMDiff_compactFamily_of_joint
    {M : Type*} [TopologicalSpace M] [ChartedSpace V M] [IsManifold 𝓘(ℝ, V) ∞ M]
    (j : C(X, N)) {h : M × N → E}
    (hh : ContMDiff (𝓘(ℝ, V).prod 𝓘(ℝ, W)) 𝓘(ℝ, E) ∞ h)
    {f : M → C(X, E)} (heq : ∀ y a, f y a = h (y, j a)) :
    ContMDiff 𝓘(ℝ, V) 𝓘(ℝ, C(X, E)) ∞ f := by
  intro p
  let c := extChartAt 𝓘(ℝ, V) p
  have hct : IsOpen c.target := (chartAt V p).isOpen_extend_target
  have hci : ContMDiffOn 𝓘(ℝ, V) 𝓘(ℝ, V) ∞ c.symm c.target := contMDiffOn_extChartAt_symm p
  have hloc : ContMDiffOn (𝓘(ℝ, V).prod 𝓘(ℝ, W)) 𝓘(ℝ, E) ∞
      (fun q : V × N => h (c.symm q.1, q.2)) (c.target ×ˢ univ) :=
    hh.comp_contMDiffOn (hci.prodMap contMDiff_id.contMDiffOn)
  have hsm : ContDiffOn ℝ ∞ (f ∘ c.symm) c.target :=
    contDiffOn_infty.mpr fun m => contDiffOn_nat_of_joint_manifold j hct m hloc
      (fun y _ a => heq (c.symm y) a)
  rw [contMDiffAt_iff_source, ModelWithCorners.range_eq_univ, contMDiffWithinAt_univ]
  exact (hsm.contDiffAt (hct.mem_nhds (mem_extChartAt_target p))).contMDiffAt

end Langlands.Analysis
