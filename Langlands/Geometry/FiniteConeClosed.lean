/-
Copyright (c) 2020 Kim Morrison. All rights reserved.
Released under Apache 2.0 license as described in the Mathlib LICENSE.
Authors: Johan Commelin, Kim Morrison; conic adaptation by Worker 705
-/
import Mathlib.Geometry.Convex.Cone.Pointed
import Mathlib.LinearAlgebra.LinearIndependent.Defs
import Mathlib.LinearAlgebra.Finsupp.LinearCombination
import Mathlib.Topology.Algebra.Module.FiniteDimension
import Mathlib.LinearAlgebra.Basis.VectorSpace
import Mathlib.Tactic.Linarith

/-! # Closedness of finitely generated real cones -/

noncomputable section

open Finset

namespace Langlands.Geometry.FiniteCone

variable {E : Type*} [AddCommGroup E] [Module ℝ E]

/-- Membership in a finite conic hull, using real coefficients. -/
theorem mem_hull_finset {s : Finset E} {x : E} :
    x ∈ PointedCone.hull ℝ (s : Set E) ↔
      ∃ f : E → ℝ, (∀ i ∈ s, 0 ≤ f i) ∧ ∑ i ∈ s, f i • i = x := by
  constructor
  · intro hx
    obtain ⟨f, -, hf⟩ := Submodule.mem_span_finset.mp hx
    exact ⟨fun i => (f i : ℝ), fun i _ => (f i).2, hf⟩
  · rintro ⟨f, hf, rfl⟩
    exact Submodule.sum_mem _ fun i hi =>
      (PointedCone.hull ℝ (s : Set E)).smul_mem
        (hf i hi) (PointedCone.subset_hull hi)

/-- A dependent finite family admits a relation with a positive coefficient. -/
theorem exists_positive_relation {s : Finset E}
    (hs : ¬ LinearIndepOn ℝ id (s : Set E)) :
    ∃ g : E → ℝ, (∑ i ∈ s, g i • i = 0) ∧ ∃ i ∈ s, 0 < g i := by
  obtain ⟨g, hg, i, hi, hgi⟩ := not_linearIndepOn_finset_iff.mp hs
  by_cases hp : 0 < g i
  · exact ⟨g, hg, i, hi, hp⟩
  · refine ⟨fun j => -g j, ?_, i, hi, ?_⟩
    · simpa only [id_eq, neg_smul, sum_neg_distrib, neg_zero] using congrArg Neg.neg hg
    · exact neg_pos.mpr (lt_of_le_of_ne (le_of_not_gt hp) hgi)

/-- Eliminate one generator from a conic combination of a dependent finite family.
The minimum-ratio construction follows Mathlib's convex Caratheodory proof. -/
theorem mem_hull_erase [DecidableEq E] {s : Finset E}
    (hs : ¬ LinearIndepOn ℝ id (s : Set E)) {x : E}
    (hx : x ∈ PointedCone.hull ℝ (s : Set E)) :
    ∃ i ∈ s, x ∈ PointedCone.hull ℝ (s.erase i : Set E) := by
  obtain ⟨f, hf, rfl⟩ := mem_hull_finset.mp hx
  obtain ⟨g, hg, hp⟩ := exists_positive_relation hs
  let t := s.filter fun i => 0 < g i
  obtain ⟨i₀, hi₀, hmin⟩ : ∃ i₀ ∈ t, ∀ i ∈ t, f i₀ / g i₀ ≤ f i / g i := by
    apply t.exists_min_image fun i => f i / g i
    obtain ⟨i, hi, hgi⟩ := hp
    exact ⟨i, mem_filter.mpr ⟨hi, hgi⟩⟩
  have hgi₀ : 0 < g i₀ := (mem_filter.mp hi₀).2
  have hsi₀ : i₀ ∈ s := (mem_filter.mp hi₀).1
  let c : E → ℝ := fun i => f i - f i₀ / g i₀ * g i
  have hc₀ : c i₀ = 0 := by simp [c, ne_of_gt hgi₀]
  refine ⟨i₀, hsi₀, mem_hull_finset.mpr ⟨c, ?_, ?_⟩⟩
  · intro i hi
    have his : i ∈ s := mem_of_mem_erase hi
    change 0 ≤ f i - f i₀ / g i₀ * g i
    rw [sub_nonneg]
    by_cases hit : i ∈ t
    · exact (le_div_iff₀ (mem_filter.mp hit).2).mp (hmin i hit)
    · calc
        f i₀ / g i₀ * g i ≤ 0 := mul_nonpos_of_nonneg_of_nonpos
          (div_nonneg (hf i₀ hsi₀) hgi₀.le)
          (by simpa only [t, mem_filter, his, true_and, not_lt] using hit)
        _ ≤ f i := hf i his
  · calc
      ∑ i ∈ s.erase i₀, c i • i = ∑ i ∈ s, c i • i :=
        sum_erase _ (by rw [hc₀, zero_smul])
      _ = ∑ i ∈ s, f i • i := by
        simp only [c, sub_smul, mul_smul, sum_sub_distrib, ← smul_sum, hg,
          smul_zero, sub_zero]

/-- Every point of a finite conic hull belongs to an independent subcone. -/
theorem exists_independent_subcone [DecidableEq E] (s : Finset E) {x : E}
    (hx : x ∈ PointedCone.hull ℝ (s : Set E)) :
    ∃ t ⊆ s, LinearIndepOn ℝ id (t : Set E) ∧
      x ∈ PointedCone.hull ℝ (t : Set E) := by
  revert hx
  refine Finset.strongInductionOn s ?_
  intro s ih hx
  by_cases hs : LinearIndepOn ℝ id (s : Set E)
  · exact ⟨s, Subset.rfl, hs, hx⟩
  · obtain ⟨i, hi, hxi⟩ := mem_hull_erase hs hx
    obtain ⟨t, ht, hti, hxt⟩ := ih (s.erase i) (erase_ssubset hi) hxi
    exact ⟨t, ht.trans (erase_subset i s), hti, hxt⟩

/-- The finite conic hull is the image of its coordinate orthant. -/
theorem hull_finset_eq_image (s : Finset E) :
    (PointedCone.hull ℝ (s : Set E) : Set E) =
      Fintype.linearCombination ℝ (fun i : s => (i : E)) ''
        {f : s → ℝ | ∀ i, 0 ≤ f i} := by
  ext x
  change x ∈ Submodule.span (Nonneg ℝ) (s : Set E) ↔ _
  rw [Submodule.mem_span_finset']
  constructor
  · rintro ⟨f, hf⟩
    refine ⟨fun i => (f i : ℝ), fun i => (f i).2, ?_⟩
    simpa only [Fintype.linearCombination_apply, Nonneg.coe_smul] using hf
  · rintro ⟨f, hf, hfx⟩
    refine ⟨fun i => ⟨f i, hf i⟩, ?_⟩
    simpa only [Fintype.linearCombination_apply, Nonneg.mk_smul] using hfx

section Topological

variable [TopologicalSpace E] [IsTopologicalAddGroup E] [ContinuousSMul ℝ E]
  [T2Space E]

/-- An independent finite conic hull is closed. -/
theorem isClosed_hull_independent (s : Finset E)
    (hs : LinearIndepOn ℝ id (s : Set E)) :
    IsClosed (PointedCone.hull ℝ (s : Set E) : Set E) := by
  rw [hull_finset_eq_image]
  have hinj : Function.Injective (Fintype.linearCombination ℝ (fun i : s => (i : E))) :=
    hs.fintypeLinearCombination_injective
  apply (LinearMap.isClosedEmbedding_of_injective (LinearMap.ker_eq_bot.mpr hinj)).isClosedMap
  simpa only [Set.ofPred_forall] using
    (isClosed_iInter fun i : s =>
      isClosed_le (continuous_const : Continuous (fun _ : s → ℝ => (0 : ℝ)))
        (continuous_apply i))

/-- A finitely generated real cone is closed in any Hausdorff real topological vector space. -/
theorem isClosed_hull_finset (s : Finset E) :
    IsClosed (PointedCone.hull ℝ (s : Set E) : Set E) := by
  classical
  let ts := s.powerset.filter fun (t : Finset E) => LinearIndepOn ℝ id (t : Set E)
  have heq : (PointedCone.hull ℝ (s : Set E) : Set E) =
      ⋃ t ∈ ts, (PointedCone.hull ℝ (t : Set E) : Set E) := by
    ext x
    constructor
    · intro hx
      obtain ⟨t, hts, ht, hxt⟩ := exists_independent_subcone s hx
      exact Set.mem_iUnion.mpr ⟨t, Set.mem_iUnion.mpr
        ⟨mem_filter.mpr ⟨mem_powerset.mpr hts, ht⟩, hxt⟩⟩
    · intro hx
      obtain ⟨t, hxt⟩ := Set.mem_iUnion.mp hx
      obtain ⟨ht, hxt⟩ := Set.mem_iUnion.mp hxt
      exact (Submodule.span_mono (mem_powerset.mp (mem_filter.mp ht).1)) hxt
  rw [heq]
  exact isClosed_biUnion_finset fun t ht =>
    isClosed_hull_independent t (mem_filter.mp ht).2

/-- Set-indexed form of finite-hull closedness. -/
theorem isClosed_hull_finite {s : Set E} (hs : s.Finite) :
    IsClosed (PointedCone.hull ℝ s : Set E) := by
  classical
  simpa only [hs.coe_toFinset] using isClosed_hull_finset hs.toFinset

end Topological

/-- The canonical module topology on a real vector space is Hausdorff. -/
theorem moduleTopology_t2Space :
    let := moduleTopology ℝ E
    T2Space E := by
  let := moduleTopology ℝ E
  let b := Module.Basis.ofVectorSpace ℝ E
  apply T2Space.of_injective_continuous (f := fun x i => b.repr x i)
  · intro x y hxy
    apply b.repr.injective
    exact Finsupp.ext fun i => congrFun hxy i
  · apply continuous_pi
    intro i
    exact IsModuleTopology.continuous_of_linearMap
      ((Finsupp.lapply i).comp b.repr.toLinearMap)

/-- Finite real conic hulls are closed for the canonical module topology. -/
theorem isClosed_hull_moduleTopology {s : Set E} (hs : s.Finite) :
    @IsClosed E (moduleTopology ℝ E) (PointedCone.hull ℝ s : Set E) := by
  let := moduleTopology ℝ E
  let := IsModuleTopology.isTopologicalAddGroup ℝ E
  let := moduleTopology_t2Space (E := E)
  exact isClosed_hull_finite hs

end Langlands.Geometry.FiniteCone
