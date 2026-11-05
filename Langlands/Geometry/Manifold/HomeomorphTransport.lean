import Mathlib.Geometry.Manifold.Diffeomorph

/-! # Explicit pullback of manifold charts along an actual homeomorphism -/

noncomputable section

open Set Function
open scoped Manifold ContDiff

namespace Langlands.Geometry.Manifold

variable {H M N : Type*} [TopologicalSpace H] [TopologicalSpace M]
  [TopologicalSpace N] [ChartedSpace H N]

/-- Pull the specified target charts back along `e`, retaining the given source topology. -/
@[instance_reducible]
def pullbackChartedSpace (e : M ≃ₜ N) : ChartedSpace H M where
  atlas := (fun c => e.transOpenPartialHomeomorph c) '' atlas H N
  chartAt x := e.transOpenPartialHomeomorph (chartAt H (e x))
  mem_chart_source x := mem_chart_source H (e x)
  chart_mem_atlas x := mem_image_of_mem _ (chart_mem_atlas H (e x))

omit [ChartedSpace H N] in
/-- Transitions between the pulled charts are exactly the original transitions. -/
theorem pullbackChart_transition (e : M ≃ₜ N) (c c' : OpenPartialHomeomorph N H) :
    (e.transOpenPartialHomeomorph c).symm.trans (e.transOpenPartialHomeomorph c') =
      c.symm.trans c' := by
  apply OpenPartialHomeomorph.ext
  · intro x
    change c' (e (e.symm (c.symm x))) = c' (c.symm x)
    rw [e.apply_symm_apply]
  · intro x
    change c (e (e.symm (c'.symm x))) = c (c'.symm x)
    rw [e.apply_symm_apply]
  · ext x
    change (x ∈ c.target ∧ e (e.symm (c.symm x)) ∈ c'.source) ↔
      (x ∈ c.target ∧ c.symm x ∈ c'.source)
    rw [e.apply_symm_apply]

variable {𝕜 : Type*} [NontriviallyNormedField 𝕜]
  {E : Type*} [NormedAddCommGroup E] [NormedSpace 𝕜 E]
  (I : ModelWithCorners 𝕜 E H) (n : ℕ∞ω)

/-- The pullback atlas is a manifold whenever the specified target atlas is. -/
theorem pullbackIsManifold (e : M ≃ₜ N) [IsManifold I n N] :
    let _ := pullbackChartedSpace (H := H) e
    IsManifold I n M := by
  let _ := pullbackChartedSpace (H := H) e
  refine { compatible := ?_ }
  intro c c' hc hc'
  obtain ⟨a, ha, rfl⟩ := hc
  obtain ⟨a', ha', rfl⟩ := hc'
  rw [pullbackChart_transition]
  exact (contDiffGroupoid n I).compatible ha ha'

/-- The actual homeomorphism is smooth for these pulled charts. -/
theorem contMDiff_pullback_toFun (e : M ≃ₜ N) :
    let _ := pullbackChartedSpace (H := H) e
    ContMDiff I I n e := by
  let _ := pullbackChartedSpace (H := H) e
  dsimp only
  intro x
  rw [contMDiffAt_iff]
  refine ⟨e.continuous.continuousAt, ?_⟩
  have h := (contMDiffAt_iff.mp (contMDiffAt_id (M := N) (I := I) (n := n) (x := e x))).2
  change ContDiffWithinAt 𝕜 n
    (fun y => I (chartAt H (e x) (e (e.symm ((chartAt H (e x)).symm (I.symm y))))))
    (range I) (I (chartAt H (e x) (e x)))
  simpa only [extChartAt_coe, extChartAt_coe_symm, Function.comp_def, id_eq,
    Homeomorph.apply_symm_apply] using h

/-- The actual inverse is smooth for the same pulled charts. -/
theorem contMDiff_pullback_invFun (e : M ≃ₜ N) :
    let _ := pullbackChartedSpace (H := H) e
    ContMDiff I I n e.symm := by
  let _ := pullbackChartedSpace (H := H) e
  dsimp only
  intro x
  rw [contMDiffAt_iff]
  refine ⟨e.symm.continuous.continuousAt, ?_⟩
  have h := (contMDiffAt_iff.mp (contMDiffAt_id (M := N) (I := I) (n := n) (x := x))).2
  change ContDiffWithinAt 𝕜 n
    (fun y => I (chartAt H (e (e.symm x))
      (e (e.symm ((chartAt H x).symm (I.symm y))))))
    (range I) (I (chartAt H x x))
  simpa only [extChartAt_coe, extChartAt_coe_symm, Function.comp_def, id_eq,
    Homeomorph.apply_symm_apply] using h

/-- The given equivalence, with its literal maps, is a diffeomorphism from the
pulled atlas to the specified target atlas. -/
def pullbackDiffeomorph (e : M ≃ₜ N) :
    let _ := pullbackChartedSpace (H := H) e
    Diffeomorph I I M N n := by
  let _ := pullbackChartedSpace (H := H) e
  exact {
    toEquiv := e.toEquiv
    contMDiff_toFun := contMDiff_pullback_toFun I n e
    contMDiff_invFun := contMDiff_pullback_invFun I n e
  }

section Families

variable {F P : Type*} [NormedAddCommGroup F] [NormedSpace 𝕜 F]
  {K : Type*} [TopologicalSpace K] [TopologicalSpace P] [ChartedSpace K P]
  (J : ModelWithCorners 𝕜 F K)

/-- Smooth families in the pulled atlas are exactly those whose image under
 the actual homeomorphism is smooth in the specified target atlas. -/
theorem contMDiff_pullback_iff (e : M ≃ₜ N) (f : P → M) :
    letI := pullbackChartedSpace (H := H) e
    ContMDiff J I n f ↔ ContMDiff J I n (e ∘ f) := by
  let _ := pullbackChartedSpace (H := H) e
  constructor
  · exact fun h => (contMDiff_pullback_toFun I n e).comp h
  · intro h
    simpa only [Function.comp_def, Homeomorph.symm_apply_apply] using
      (contMDiff_pullback_invFun I n e).comp h

/-- Maps out of the pulled atlas are smooth exactly when their expression on
 the specified target atlas is smooth. -/
theorem contMDiff_from_pullback_iff (e : M ≃ₜ N) (f : M → P) :
    letI := pullbackChartedSpace (H := H) e
    ContMDiff I J n f ↔ ContMDiff I J n (f ∘ e.symm) := by
  let _ := pullbackChartedSpace (H := H) e
  constructor
  · exact fun h => h.comp (contMDiff_pullback_invFun I n e)
  · intro h
    simpa only [Function.comp_def, Homeomorph.symm_apply_apply] using
      h.comp (contMDiff_pullback_toFun I n e)

end Families

end Langlands.Geometry.Manifold
