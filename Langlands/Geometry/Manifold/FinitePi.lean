import Mathlib.Geometry.Manifold.ContMDiff.Constructions

/-! # Finite products of manifolds with normed-vector-space chart models -/

noncomputable section

open Set Function
open scoped Manifold ContDiff

namespace Langlands.Geometry.Manifold

variable {𝕜 : Type*} [NontriviallyNormedField 𝕜]
  {ι : Type*} [Fintype ι]
  (E : ι → Type*) [∀ i, NormedAddCommGroup (E i)] [∀ i, NormedSpace 𝕜 (E i)]
  (M : ι → Type*) [∀ i, TopologicalSpace (M i)] [∀ i, ChartedSpace (E i) (M i)]

/-- The usual finite product charts, explicitly using the normed Pi model. -/
@[instance_reducible]
def finitePiChartedSpace : ChartedSpace (∀ i, E i) (∀ i, M i) :=
  piChartedSpace E M

/-- A finite product of manifolds without boundary, with the specified product charts. -/
theorem finitePiIsManifold (n : ℕ∞ω) [∀ i, IsManifold 𝓘(𝕜, E i) n (M i)] :
    letI := finitePiChartedSpace E M
    IsManifold 𝓘(𝕜, ∀ i, E i) n (∀ i, M i) := by
  let := finitePiChartedSpace E M
  refine isManifold_of_contDiffOn _ _ _ fun c c' hc hc' => ?_
  obtain ⟨e, he, rfl⟩ := hc
  obtain ⟨e', he', rfl⟩ := hc'
  rw [modelWithCornersSelf_coe, modelWithCornersSelf_coe_symm, range_id, inter_univ,
    preimage_id, Function.id_comp, Function.comp_id]
  apply contDiffOn_pi.2
  intro i
  have h := ((contDiffGroupoid n 𝓘(𝕜, E i)).compatible
    (he i trivial) (he' i trivial)).1
  have hlocal : ContDiffOn 𝕜 n ((e i).symm.trans (e' i))
      ((e i).symm.trans (e' i)).source := by
    simpa only [contDiffPregroupoid, modelWithCornersSelf_coe,
      modelWithCornersSelf_coe_symm, range_id,
      inter_univ, preimage_id, Function.id_comp, Function.comp_id] using h
  exact hlocal.comp (contDiff_pi.mp
    (contDiff_id : ContDiff 𝕜 n (id : (∀ i, E i) → ∀ i, E i)) i).contDiffOn
    (fun x hx => ⟨hx.1 i trivial, hx.2 i trivial⟩)

variable {F : Type*} [NormedAddCommGroup F] [NormedSpace 𝕜 F]
  {H : Type*} [TopologicalSpace H] (I : ModelWithCorners 𝕜 F H)
  {P : Type*} [TopologicalSpace P] [ChartedSpace H P]

/-- Smoothness at a point into the finite product is componentwise. -/
theorem contMDiffAt_finitePi_iff (n : ℕ∞ω) (f : P → ∀ i, M i) (x : P) :
    letI := finitePiChartedSpace E M
    ContMDiffAt I 𝓘(𝕜, ∀ i, E i) n f x ↔
      ∀ i, ContMDiffAt I 𝓘(𝕜, E i) n (fun y => f y i) x := by
  let := finitePiChartedSpace E M
  simp only [contMDiffAt_iff, continuousAt_pi, contDiffWithinAt_pi, forall_and,
    extChartAt_coe, modelWithCornersSelf_coe, Function.comp_def]
  rfl

/-- Smooth families into the finite product are exactly the componentwise smooth families. -/
theorem contMDiff_finitePi_iff (n : ℕ∞ω) (f : P → ∀ i, M i) :
    letI := finitePiChartedSpace E M
    ContMDiff I 𝓘(𝕜, ∀ i, E i) n f ↔
      ∀ i, ContMDiff I 𝓘(𝕜, E i) n (fun y => f y i) := by
  let := finitePiChartedSpace E M
  exact ⟨fun hf i x => (contMDiffAt_finitePi_iff E M I n f x).mp (hf x) i,
    fun hf x => (contMDiffAt_finitePi_iff E M I n f x).mpr fun i => hf i x⟩

end Langlands.Geometry.Manifold
