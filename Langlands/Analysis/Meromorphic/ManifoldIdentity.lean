import Mathlib.Analysis.Complex.CauchyIntegral
import Mathlib.Analysis.Analytic.Uniqueness
import Mathlib.Analysis.LocallyConvex.SeparatingDual
import Mathlib.Geometry.Manifold.MFDeriv.Atlas
import Mathlib.Geometry.Manifold.MFDeriv.FDeriv

/-! # Charts, the identity theorem and separation by complex linear forms

Auxiliary facts for the proof of the principle of meromorphic continuation
(Bernstein–Lapid, Theorem 3.3) on a complex manifold `M` charted on a complex
normed space `E` with model `𝓘(ℂ, E)`:

* transport of complex differentiability of scalar functions between `M` and a
  chart (`differentiableOn_comp_chartAt_symm`, `mdifferentiableOn_comp_chartAt`);
* the identity theorem on convex open subsets of `E`, proved by restriction to
  complex lines (`eqOn_zero_of_convex_of_eqOn_zero`), and on chart balls in `M`
  (`ChartBall.eqOn_zero`);
* continuous complex linear forms separate the points of a Hausdorff locally
  convex complex space (`separatingDual_complex`). -/

noncomputable section
set_option autoImplicit false

namespace Langlands.Analysis.Meromorphic

open Set Filter Topology
open scoped Manifold

section Separation

variable {F : Type*} [AddCommGroup F] [Module ℂ F] [Module ℝ F] [IsScalarTower ℝ ℂ F]
  [TopologicalSpace F] [IsTopologicalAddGroup F] [ContinuousSMul ℂ F]
  [LocallyConvexSpace ℝ F] [T1Space F]

/-- Continuous complex linear forms separate the points of a complex locally
convex space whose topology is `T₁` (complex form of the geometric Hahn–Banach
theorem). -/
theorem separatingDual_complex : SeparatingDual ℂ F :=
  ⟨fun _x hx => (RCLike.geometric_hahn_banach_point_point (𝕜 := ℂ) hx).imp
    fun f hf hf' => by simp [hf'] at hf⟩

/-- Two vectors of a complex locally convex `T₁` space agree when all continuous
complex linear forms agree on them. -/
theorem eq_of_forall_clm_apply_eq {x y : F} (h : ∀ φ : F →L[ℂ] ℂ, φ x = φ y) : x = y := by
  have := (separatingDual_complex : SeparatingDual ℂ F)
  exact (SeparatingDual.eq_iff_forall_dual_eq (R := ℂ)).2 h

end Separation

section IdentityVector

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]

/-- The identity theorem on a convex open set of a complex normed space: a
complex differentiable function on `B` vanishing on a nonempty open subset of `B`
vanishes on `B`. The proof restricts to complex lines through a point of `O`. -/
theorem eqOn_zero_of_convex_of_eqOn_zero {g : E → ℂ} {B O : Set E} (hB : IsOpen B)
    (hBc : Convex ℝ B) (hg : DifferentiableOn ℂ g B) (hO : IsOpen O) (hOB : O ⊆ B)
    (hOne : O.Nonempty) (hgO : EqOn g 0 O) : EqOn g 0 B := by
  obtain ⟨p, hpO⟩ := hOne
  intro x hx
  set L : ℂ → E := fun z => p + z • (x - p) with hL
  have hLc : Continuous L := by fun_prop
  set D : Set ℂ := L ⁻¹' B with hD
  have hDo : IsOpen D := hB.preimage hLc
  have hDc : Convex ℝ D := by
    intro z₁ hz₁ z₂ hz₂ a b ha hb hab
    have key : L (a • z₁ + b • z₂) = a • L z₁ + b • L z₂ := by
      simp only [hL, add_smul, smul_add, smul_assoc]
      rw [add_add_add_comm, ← add_smul, hab, one_smul]
    simp only [hD, mem_preimage, key]
    exact hBc hz₁ hz₂ ha hb hab
  have hφ : DifferentiableOn ℂ (g ∘ L) D := by
    refine hg.comp (fun z _ => ?_) (fun z hz => hz)
    exact ((differentiableAt_const _).add
      (differentiableAt_id.smul_const (x - p))).differentiableWithinAt
  have h0D : (0 : ℂ) ∈ D := by simpa [hD, hL] using hOB hpO
  have h1D : (1 : ℂ) ∈ D := by simpa [hD, hL] using hx
  have hev : (g ∘ L) =ᶠ[𝓝 (0 : ℂ)] 0 := by
    have : L ⁻¹' O ∈ 𝓝 (0 : ℂ) :=
      (hO.preimage hLc).mem_nhds (by simpa [hL] using hpO)
    filter_upwards [this] with z hz
    exact hgO hz
  have := (hφ.analyticOnNhd hDo).eqOn_zero_of_preconnected_of_eventuallyEq_zero
    hDc.isPreconnected h0D hev h1D
  simpa [hL] using this

end IdentityVector

section Charts

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
  {M : Type*} [TopologicalSpace M] [ChartedSpace E M]

/-- A scalar function holomorphic on `W ⊆ M` is complex differentiable in the
chart at `s₀` on the chart image of `W`. -/
theorem differentiableOn_comp_chartAt_symm [IsManifold 𝓘(ℂ, E) 1 M] {h : M → ℂ} {W : Set M} (s₀ : M)
    (hh : MDifferentiableOn 𝓘(ℂ, E) 𝓘(ℂ, ℂ) h W) :
    DifferentiableOn ℂ (h ∘ (chartAt E s₀).symm)
      ((chartAt E s₀).target ∩ (chartAt E s₀).symm ⁻¹' W) := by
  have h1 := (mdifferentiableOn_atlas_symm (I := 𝓘(ℂ, E)) (chart_mem_atlas E s₀)).mono
    (inter_subset_left (t := (chartAt E s₀).symm ⁻¹' W))
  exact (hh.comp h1 (fun x hx => hx.2)).differentiableOn

/-- A function complex differentiable on a set `B` of the chart at `s₀`
gives a holomorphic function on the preimage of `B` in the chart domain. -/
theorem mdifferentiableOn_comp_chartAt [IsManifold 𝓘(ℂ, E) 1 M] {g : E → ℂ} {B : Set E} (s₀ : M)
    (hg : DifferentiableOn ℂ g B) :
    MDifferentiableOn 𝓘(ℂ, E) 𝓘(ℂ, ℂ) (g ∘ chartAt E s₀)
      ((chartAt E s₀).source ∩ chartAt E s₀ ⁻¹' B) := by
  have h1 := (mdifferentiableOn_atlas (I := 𝓘(ℂ, E)) (chart_mem_atlas E s₀)).mono
    (inter_subset_left (t := chartAt E s₀ ⁻¹' B))
  exact hg.mdifferentiableOn.comp h1 (fun x hx => hx.2)

omit [NormedSpace ℂ E] in
/-- The chart image `(chartAt E s₀).target ∩ (chartAt E s₀).symm ⁻¹' W` of an open
set `W` is open. -/
theorem isOpen_chartAt_target_inter {W : Set M} (s₀ : M) (hW : IsOpen W) :
    IsOpen ((chartAt E s₀).target ∩ (chartAt E s₀).symm ⁻¹' W) :=
  (chartAt E s₀).continuousOn_symm.isOpen_inter_preimage (chartAt E s₀).open_target hW

/-- A chart ball at `s₀`: a convex open subset `B` of the target of the chart at
`s₀`, together with the open set `W = (chartAt E s₀).symm '' B` of `M`. -/
structure ChartBall (s₀ : M) (W : Set M) : Prop where
  exists_convex : ∃ B : Set E, IsOpen B ∧ Convex ℝ B ∧ B ⊆ (chartAt E s₀).target ∧
    W = (chartAt E s₀).source ∩ chartAt E s₀ ⁻¹' B

namespace ChartBall

variable {s₀ : M} {W : Set M}

theorem isOpen (hW : ChartBall (E := E) s₀ W) : IsOpen W := by
  obtain ⟨B, hBo, -, -, rfl⟩ := hW.exists_convex
  exact (chartAt E s₀).continuousOn.isOpen_inter_preimage (chartAt E s₀).open_source hBo

theorem subset_source (hW : ChartBall (E := E) s₀ W) : W ⊆ (chartAt E s₀).source := by
  obtain ⟨B, -, -, -, rfl⟩ := hW.exists_convex
  exact inter_subset_left

theorem isPreconnected (hW : ChartBall (E := E) s₀ W) : IsPreconnected W := by
  obtain ⟨B, -, hBc, hBt, rfl⟩ := hW.exists_convex
  rw [← (chartAt E s₀).symm_image_eq_source_inter_preimage hBt]
  exact hBc.isPreconnected.image _ ((chartAt E s₀).continuousOn_symm.mono hBt)

/-- The identity theorem on a chart ball. -/
theorem eqOn_zero [IsManifold 𝓘(ℂ, E) 1 M] (hW : ChartBall (E := E) s₀ W) {h : M → ℂ}
    (hh : MDifferentiableOn 𝓘(ℂ, E) 𝓘(ℂ, ℂ) h W) {O : Set M} (hO : IsOpen O)
    (hOW : O ⊆ W) (hOne : O.Nonempty) (hhO : EqOn h 0 O) : EqOn h 0 W := by
  obtain ⟨B, hBo, hBc, hBt, rfl⟩ := hW.exists_convex
  set e := chartAt E s₀ with he
  have hBW : B ⊆ e.target ∩ e.symm ⁻¹' (e.source ∩ e ⁻¹' B) := by
    intro x hx
    refine ⟨hBt hx, e.map_target (hBt hx), ?_⟩
    simpa [e.right_inv (hBt hx)] using hx
  have hg : DifferentiableOn ℂ (h ∘ e.symm) B :=
    (differentiableOn_comp_chartAt_symm s₀ hh).mono hBW
  have hO' : IsOpen (B ∩ e.symm ⁻¹' O) :=
    (e.continuousOn_symm.mono hBt).isOpen_inter_preimage hBo hO
  obtain ⟨s, hsO⟩ := hOne
  have hsB : e s ∈ B ∩ e.symm ⁻¹' O := by
    have hsW := hOW hsO
    refine ⟨hsW.2, ?_⟩
    simpa [mem_preimage, e.left_inv hsW.1] using hsO
  have hzero := eqOn_zero_of_convex_of_eqOn_zero hBo hBc hg hO' inter_subset_left
    ⟨e s, hsB⟩ (fun x hx => hhO hx.2)
  intro t ht
  have := hzero ht.2
  simpa [e.left_inv ht.1] using this

end ChartBall

/-- Every neighborhood of a point contains a chart ball at that point. -/
theorem exists_chartBall_subset (s₀ : M) {U : Set M} (hU : U ∈ 𝓝 s₀) :
    ∃ W : Set M, ChartBall (E := E) s₀ W ∧ s₀ ∈ W ∧ W ⊆ U := by
  set e := chartAt E s₀ with he
  have hmem : e.target ∩ e.symm ⁻¹' interior U ∈ 𝓝 (e s₀) := by
    refine (isOpen_chartAt_target_inter s₀ isOpen_interior).mem_nhds ⟨e.map_source
      (mem_chart_source E s₀), ?_⟩
    show e.symm (e s₀) ∈ interior U
    rw [e.left_inv (mem_chart_source E s₀)]
    exact mem_interior_iff_mem_nhds.2 hU
  obtain ⟨r, hr, hrB⟩ := Metric.mem_nhds_iff.1 hmem
  refine ⟨e.source ∩ e ⁻¹' Metric.ball (e s₀) r,
    ⟨⟨Metric.ball (e s₀) r, Metric.isOpen_ball, convex_ball _ _,
      fun x hx => (hrB hx).1, rfl⟩⟩, ⟨mem_chart_source E s₀, Metric.mem_ball_self hr⟩, ?_⟩
  intro t ht
  have := (hrB ht.2).2
  rw [mem_preimage, e.left_inv ht.1] at this
  exact interior_subset this

end Charts

end Langlands.Analysis.Meromorphic
