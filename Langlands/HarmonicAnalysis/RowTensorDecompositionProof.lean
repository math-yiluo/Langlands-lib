import Langlands.HarmonicAnalysis.RowTensorDecompositionStatement
import Mathlib.Topology.Separation.Profinite
import Mathlib.LinearAlgebra.Finsupp.LinearCombination

/-!
# Finite tensor decomposition of row Schwartz–Bruhat functions

Compact-open boxes on which a test function is constant cover its compact
support. A finite-union indicator identity places the function in the linear
span of pure pointwise tensors. Enumerating a finitely supported linear
combination gives the exact published statement.
-/

noncomputable section

open Set Filter
open scoped BigOperators Topology

namespace Langlands.HarmonicAnalysis

universe u

variable {X : Type u} [TopologicalSpace X] {d : ℕ}

private def rowPure (g : Fin d → SchwartzBruhat X) : (Fin d → X) → ℂ :=
  fun x => ∏ i, g i (x i)

private def rowSpan (X : Type u) [TopologicalSpace X] (d : ℕ) :
    Submodule ℂ ((Fin d → X) → ℂ) :=
  Submodule.span ℂ (Set.range (rowPure (X := X) (d := d)))

private theorem rowPure_mem (g : Fin d → SchwartzBruhat X) :
    rowPure g ∈ rowSpan X d := Submodule.subset_span ⟨g, rfl⟩

private def sbMul (g h : SchwartzBruhat X) : SchwartzBruhat X :=
  ⟨(g : X → ℂ) * h, g.locallyConstant.mul h.locallyConstant,
    g.hasCompactSupport.mul_right⟩

private theorem rowSpan_mul_pure {f : (Fin d → X) → ℂ}
    (hf : f ∈ rowSpan X d) (g : Fin d → SchwartzBruhat X) :
    f * rowPure g ∈ rowSpan X d := by
  induction hf using Submodule.span_induction with
  | mem y hy =>
    rcases hy with ⟨h, rfl⟩
    have heq : rowPure h * rowPure g = rowPure (fun i => sbMul (h i) (g i)) := by
      funext x
      exact (Finset.prod_mul_distrib).symm
    rw [heq]
    exact rowPure_mem _
  | zero => simp
  | add y z _ _ hy hz =>
    simpa only [add_mul] using (rowSpan X d).add_mem hy hz
  | smul c y _ hy =>
    simpa only [smul_mul_assoc] using (rowSpan X d).smul_mem c hy

private def compactClopenIndicator [T2Space X] (U : Set X)
    (hUc : IsCompact U) (hUo : IsClopen U) : SchwartzBruhat X :=
  ⟨U.indicator (fun _ => 1),
    ((LocallyConstant.const X (1 : ℂ)).indicator hUo).isLocallyConstant,
    HasCompactSupport.intro hUc (fun _ hx => Set.indicator_of_notMem hx _)⟩

private theorem box_indicator [T2Space X] (U : Fin d → Set X)
    (hUc : ∀ i, IsCompact (U i)) (hUo : ∀ i, IsClopen (U i)) :
    (Set.pi Set.univ U).indicator (fun _ => (1 : ℂ)) =
      rowPure (fun i => compactClopenIndicator (U i) (hUc i) (hUo i)) := by
  classical
  funext x
  by_cases hx : x ∈ Set.pi Set.univ U
  · rw [Set.indicator_of_mem hx]
    symm
    apply Finset.prod_eq_one
    intro i _
    change (U i).indicator (fun _ => (1 : ℂ)) (x i) = 1
    exact Set.indicator_of_mem (hx i (Set.mem_univ i)) _
  · rw [Set.indicator_of_notMem hx]
    simp only [Set.mem_pi, Set.mem_univ, forall_true_left, not_forall] at hx
    obtain ⟨i, hi⟩ := hx
    symm
    apply Finset.prod_eq_zero (Finset.mem_univ i)
    change (U i).indicator (fun _ => (1 : ℂ)) (x i) = 0
    exact Set.indicator_of_notMem hi _

private theorem exists_compact_clopen [LocallyCompactSpace X] [T2Space X]
    [TotallyDisconnectedSpace X] {x : X} {V : Set X} (hV : V ∈ 𝓝 x) :
    ∃ U : Set X, IsCompact U ∧ IsClopen U ∧ x ∈ U ∧ U ⊆ V := by
  obtain ⟨K, hKc, hK⟩ := exists_compact_mem_nhds x
  obtain ⟨U, hU, hx, hUVK⟩ :=
    loc_compact_Haus_tot_disc_of_zero_dim.mem_nhds_iff.mp (inter_mem hV hK)
  exact ⟨U, hKc.of_isClosed_subset hU.isClosed (fun y hy => (hUVK hy).2),
    hU, hx, fun y hy => (hUVK hy).1⟩

private theorem exists_constant_box [LocallyCompactSpace X] [T2Space X]
    [TotallyDisconnectedSpace X] (f : SchwartzBruhat (Fin d → X)) (x : Fin d → X) :
    ∃ U : Fin d → Set X, (∀ i, IsCompact (U i)) ∧ (∀ i, IsClopen (U i)) ∧
      x ∈ Set.pi Set.univ U ∧ ∀ y ∈ Set.pi Set.univ U, f y = f x := by
  have hf := f.locallyConstant.eventually_eq x
  rw [nhds_pi] at hf
  obtain ⟨I, _, V, hV, hVf⟩ := Filter.mem_pi.mp hf
  choose U hUc hUo hxU hUV using fun i => exists_compact_clopen (hV i)
  refine ⟨U, hUc, hUo, fun i _ => hxU i, ?_⟩
  intro y hy
  exact hVf (fun i _ => hUV i (hy i (Set.mem_univ i)))

private theorem rowSpan_indicator_union {α : Type*} (f : (Fin d → X) → ℂ)
    (U : α → Set (Fin d → X)) (g : α → Fin d → SchwartzBruhat X)
    (hU : ∀ a, (U a).indicator (fun _ => (1 : ℂ)) = rowPure (g a))
    (hf : ∀ a, (U a).indicator f ∈ rowSpan X d) (s : Finset α) :
    (⋃ a ∈ s, U a).indicator f ∈ rowSpan X d := by
  classical
  induction s using Finset.induction_on with
  | empty =>
    convert (rowSpan X d).zero_mem using 1
    ext x
    simp
  | @insert a s _ ih =>
    have hm := rowSpan_mul_pure ih (g a)
    rw [← hU a] at hm
    have heq : (⋃ b ∈ insert a s, U b).indicator f =
        (U a).indicator f + (⋃ b ∈ s, U b).indicator f -
          (⋃ b ∈ s, U b).indicator f * (U a).indicator (fun _ => (1 : ℂ)) := by
      funext x
      simp only [Finset.set_biUnion_insert, Pi.sub_apply, Pi.add_apply, Pi.mul_apply]
      by_cases ha : x ∈ U a <;> by_cases hs : x ∈ ⋃ b ∈ s, U b <;>
        simp [Set.indicator, ha, hs]
    rw [heq]
    exact (rowSpan X d).sub_mem ((rowSpan X d).add_mem (hf a) ih) hm

private theorem row_mem_span [LocallyCompactSpace X] [T2Space X]
    [TotallyDisconnectedSpace X] (f : SchwartzBruhat (Fin d → X)) :
    (f : (Fin d → X) → ℂ) ∈ rowSpan X d := by
  classical
  choose U hUc hUo hxU hUf using exists_constant_box f
  let B (x : Fin d → X) : Set (Fin d → X) := Set.pi Set.univ (U x)
  let g (x : Fin d → X) (i : Fin d) : SchwartzBruhat X :=
    compactClopenIndicator (U x i) (hUc x i) (hUo x i)
  have hB (x) : (B x).indicator (fun _ => (1 : ℂ)) = rowPure (g x) :=
    box_indicator (U x) (hUc x) (hUo x)
  have hfB (x) : (B x).indicator (f : (Fin d → X) → ℂ) ∈ rowSpan X d := by
    have heq : (B x).indicator (f : (Fin d → X) → ℂ) = f x • rowPure (g x) := by
      rw [← hB x]
      funext y
      by_cases hy : y ∈ B x
      · simp [Set.indicator_of_mem hy, hUf x y hy]
      · simp [Set.indicator_of_notMem hy]
    rw [heq]
    exact (rowSpan X d).smul_mem (f x) (rowPure_mem _)
  obtain ⟨s, hs⟩ := f.hasCompactSupport.elim_finite_subcover B
    (fun x => isOpen_set_pi Set.finite_univ (fun i _ => (hUo x i).isOpen))
    (fun x _ => Set.mem_iUnion.mpr ⟨x, hxU x⟩)
  have heq : (⋃ a ∈ s, B a).indicator (f : (Fin d → X) → ℂ) = f := by
    funext x
    by_cases hx : x ∈ ⋃ a ∈ s, B a
    · exact Set.indicator_of_mem hx _
    · rw [Set.indicator_of_notMem hx]
      exact (image_eq_zero_of_notMem_tsupport (fun ht => hx (hs ht))).symm
  rw [← heq]
  exact rowSpan_indicator_union _ B g hB hfB s

/-- Every row Schwartz–Bruhat function is a finite linear combination of
pointwise products of one-coordinate Schwartz–Bruhat functions. -/
theorem rowTensorDecomposition (X : Type u) [TopologicalSpace X]
    [LocallyCompactSpace X] [T2Space X] [TotallyDisconnectedSpace X] (d : ℕ) :
    RowTensorDecompositionStatement X d := by
  classical
  intro f
  obtain ⟨c, hc⟩ := Finsupp.mem_span_range_iff_exists_finsupp.mp (row_mem_span f)
  let e := (Fintype.equivFin ↥c.support).symm
  refine ⟨Fintype.card ↥c.support, (fun j => c (e j).1), (fun j => (e j).1), ?_⟩
  intro x
  have hcx := congrFun hc x
  change (∑ g ∈ c.support, c g • rowPure g) x = f x at hcx
  rw [← hcx]
  simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul]
  have he := e.sum_comp (fun j : ↥c.support => c j.1 * rowPure j.1 x)
  rw [← Finset.sum_attach c.support (fun g => c g * rowPure g x)]
  exact he.symm

end Langlands.HarmonicAnalysis
