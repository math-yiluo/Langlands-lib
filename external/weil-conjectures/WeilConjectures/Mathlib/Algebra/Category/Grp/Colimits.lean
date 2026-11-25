/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import Mathlib.Algebra.Category.Grp.Colimits
public import Mathlib.Algebra.Group.Subgroup.Basic
public import Mathlib.Algebra.BigOperators.Group.Finset.Basic

/-!
# Elements of coproducts of abelian groups

For a colimit cofan `d` on a family `G` of abelian groups, every element of the vertex is a
finite sum of images of elements of the `G i`
(`AddCommGrpCat.exists_eq_sum_of_isColimit_cofan`). In particular a morphism out of the vertex
admitting "coordinate" retractions is injective
(`AddCommGrpCat.injective_of_isColimit_cofan`).
-/

@[expose] public section

universe w u

open CategoryTheory Limits

namespace AddCommGrpCat

variable {ι : Type w} {G : ι → AddCommGrpCat.{u}} {d : Cofan G}

/-- **Elements of a coproduct of abelian groups are finite sums.** -/
lemma exists_eq_sum_of_isColimit_cofan (hd : IsColimit d) (p : d.pt) :
    ∃ (T : Finset ι) (a : ∀ i, G i), p = ∑ i ∈ T, d.inj i (a i) := by
  classical
  let H : AddSubgroup d.pt := AddSubgroup.closure (⋃ i, Set.range (d.inj i))
  have hH : H = ⊤ := by
    let q : d.pt ⟶ AddCommGrpCat.of (d.pt ⧸ H) := AddCommGrpCat.ofHom (QuotientAddGroup.mk' H)
    have hq : q = 0 := Cofan.IsColimit.hom_ext hd _ _ fun i ↦ by
      ext a
      exact (QuotientAddGroup.eq_zero_iff _).2
        (AddSubgroup.subset_closure (Set.mem_iUnion.2 ⟨i, a, rfl⟩))
    refine eq_top_iff.2 fun p _ ↦ (QuotientAddGroup.eq_zero_iff p).1 ?_
    exact congrArg (fun f ↦ f p) (congrArg AddCommGrpCat.Hom.hom hq)
  have hp : p ∈ H := hH ▸ AddSubgroup.mem_top p
  induction hp using AddSubgroup.closure_induction with
  | mem p hp =>
    obtain ⟨i, a, rfl⟩ := Set.mem_iUnion.1 hp
    exact ⟨{i}, fun j ↦ if h : j = i then h ▸ a else 0, by simp⟩
  | zero => exact ⟨∅, 0, by simp⟩
  | add p q _ _ hp hq =>
    obtain ⟨T, a, rfl⟩ := hp
    obtain ⟨T', a', rfl⟩ := hq
    refine ⟨T ∪ T', fun i ↦ (if i ∈ T then a i else 0) + (if i ∈ T' then a' i else 0), ?_⟩
    simp only [map_add, Finset.sum_add_distrib]
    congr 1
    · rw [← Finset.sum_subset Finset.subset_union_left]
      · exact Finset.sum_congr rfl fun i hi ↦ by simp [hi]
      · intro i _ hi
        simp [hi]
    · rw [← Finset.sum_subset Finset.subset_union_right]
      · exact Finset.sum_congr rfl fun i hi ↦ by simp [hi]
      · intro i _ hi
        simp [hi]
  | neg p _ hp =>
    obtain ⟨T, a, rfl⟩ := hp
    exact ⟨T, -a, by simp⟩

/-- **A map out of a coproduct with coordinate retractions is injective.** Let `d` be a colimit
cofan on a family `G` of abelian groups, `Ψ : d.pt ⟶ C`, and `R i : C ⟶ G i` maps such that
`d.inj j ≫ Ψ ≫ R i` is the identity for `j = i` and zero otherwise. Then `Ψ` is injective. -/
lemma injective_of_isColimit_cofan (hd : IsColimit d) {C : AddCommGrpCat.{u}} (Ψ : d.pt ⟶ C)
    (R : ∀ i, C ⟶ G i) (h₁ : ∀ i, d.inj i ≫ Ψ ≫ R i = 𝟙 _)
    (h₀ : ∀ i j, j ≠ i → d.inj j ≫ Ψ ≫ R i = 0) : Function.Injective Ψ := by
  classical
  refine (injective_iff_map_eq_zero _).2 fun p hp ↦ ?_
  obtain ⟨T, a, rfl⟩ := exists_eq_sum_of_isColimit_cofan hd p
  have ha (i : ι) (hi : i ∈ T) : a i = 0 := by
    have := congrArg (R i) hp
    rw [map_zero, map_sum, map_sum, Finset.sum_eq_single i] at this
    · have e : R i (Ψ (d.inj i (a i))) = a i :=
        congrArg (fun f ↦ f (a i)) (congrArg AddCommGrpCat.Hom.hom (h₁ i))
      rw [← e]
      exact this
    · intro j _ hji
      rw [← ConcreteCategory.comp_apply, ← ConcreteCategory.comp_apply, ← Category.assoc,
        Category.assoc, h₀ i j hji]
      rfl
    · intro hi'
      exact absurd hi hi'
  exact Finset.sum_eq_zero fun i hi ↦ by rw [ha i hi, map_zero]

end AddCommGrpCat
