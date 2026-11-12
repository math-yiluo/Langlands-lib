import Langlands.Representation.Geometric.OrbitRepresentatives
import Mathlib.Order.Fin.Basic
import Mathlib.Logic.Equiv.Fin.Basic

/-! # Keeping a specified closed orbit last in an actual orbit ordering -/

noncomputable section

namespace Langlands.Geometric

universe uG

variable {G : Type uG} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
  {P Q : Subgroup G} {m : ℕ}

/-- Delete the selected index from its position and append it, keeping all
other indices in their original relative order. -/
def moveLastPermutation (p : Fin (m + 1)) : Equiv.Perm (Fin (m + 1)) :=
  (finSuccEquiv' (Fin.last m)).trans (finSuccEquiv' p).symm

@[simp]
theorem moveLastPermutation_last (p : Fin (m + 1)) :
    moveLastPermutation p (Fin.last m) = p := by
  simp [moveLastPermutation, finSuccEquiv'_at, finSuccEquiv'_symm_none]

@[simp]
theorem moveLastPermutation_castSucc (p : Fin (m + 1)) (i : Fin m) :
    moveLastPermutation p i.castSucc = p.succAbove i := by
  simp [moveLastPermutation, finSuccEquiv'_last_apply_castSucc, finSuccEquiv'_symm_some]

private theorem succAbove_threshold (p : Fin (m + 1)) (i : Fin m) (k : Fin (m + 1)) :
    (p.succAbove i).val < (p.castSucc.succAbove k).val ↔ i.val < k.val := by
  change (p.succAbove i).castSucc < p.castSucc.succAbove k ↔ i.castSucc < k
  rw [← Fin.castSucc_succAbove_castSucc, Fin.succAbove_lt_succAbove_iff]

namespace OrderedDoubleCosets

/-- A chosen closed orbit can be placed last, retaining the representatives
and the relative order of every other orbit. -/
def closedOrbitLast (s : OrderedDoubleCosets P Q (m + 1)) (p : Fin (m + 1))
    (hclosed : IsClosed (cosetOrbit P Q (s.representative p))) :
    OrderedDoubleCosets P Q (m + 1) where
  representative q := s.representative (moveLastPermutation p q)
  covers x := by
    obtain ⟨i, hi⟩ := s.covers x
    exact ⟨(moveLastPermutation p).symm i, by simpa using hi⟩
  disjoint := by
    intro i j hij
    exact s.disjoint ((moveLastPermutation p).injective.ne hij)
  initial_open k := by
    refine Fin.lastCases ?_ (fun k => ?_) k
    · have heq : {x | ∃ i : Fin (m + 1), i.val < (Fin.last (m + 1)).val ∧
          x ∈ cosetOrbit P Q (s.representative (moveLastPermutation p i))} = Set.univ := by
        ext x
        constructor
        · intro _
          trivial
        · intro _
          obtain ⟨i, hi⟩ := s.covers x
          exact ⟨(moveLastPermutation p).symm i, ((moveLastPermutation p).symm i).isLt,
            by simpa using hi⟩
      rw [heq]
      exact isOpen_univ
    · have heq : {x | ∃ i : Fin (m + 1), i.val < k.castSucc.val ∧
          x ∈ cosetOrbit P Q (s.representative (moveLastPermutation p i))} =
          {x | ∃ j : Fin (m + 1), j.val < (p.castSucc.succAbove k).val ∧
            x ∈ cosetOrbit P Q (s.representative j)} \
              cosetOrbit P Q (s.representative p) := by
        ext x
        constructor
        · rintro ⟨q, hq, hx⟩
          have hlt : q.val < m := lt_of_lt_of_le hq k.le_last
          let i : Fin m := ⟨q.val, hlt⟩
          have hi : i.castSucc = q := Fin.ext rfl
          rw [← hi, moveLastPermutation_castSucc] at hx
          refine ⟨⟨p.succAbove i, (succAbove_threshold p i k).mpr hq, hx⟩, ?_⟩
          intro hp
          exact Set.disjoint_left.mp (s.disjoint (Fin.succAbove_ne p i)) hx hp
        · rintro ⟨⟨j, hj, hx⟩, hp⟩
          have hne : j ≠ p := by
            rintro rfl
            exact hp hx
          obtain ⟨i, rfl⟩ := Fin.exists_succAbove_eq hne
          refine ⟨i.castSucc, (succAbove_threshold p i k).mp hj, ?_⟩
          simpa using hx
      rw [heq]
      exact (s.initial_open (p.castSucc.succAbove k)).sdiff hclosed

omit [IsTopologicalGroup G] in
@[simp]
theorem closedOrbitLast_representative_last
    (s : OrderedDoubleCosets P Q (m + 1)) (p : Fin (m + 1))
    (hclosed : IsClosed (cosetOrbit P Q (s.representative p))) :
    (s.closedOrbitLast p hclosed).representative (Fin.last m) = s.representative p := by
  simp [closedOrbitLast]

end OrderedDoubleCosets

omit [TopologicalSpace G] [IsTopologicalGroup G] in
/-- A representative in `P` gives the singleton identity orbit in
the self double-coset space. -/
theorem cosetOrbit_self_eq_singleton (P : Subgroup G) (w : G) (hw : w ∈ P) :
    cosetOrbit P P w = {Induction.quotientMap P 1} := by
  ext x
  constructor
  · rintro ⟨q, rfl⟩
    apply Set.mem_singleton_iff.mpr
    apply Quotient.sound
    apply QuotientGroup.rightRel_apply.mpr
    simpa only [mul_one, one_mul] using
      P.inv_mem (P.mul_mem (P.inv_mem hw) q.property)
  · rintro rfl
    refine ⟨⟨w, hw⟩, ?_⟩
    simp

end Langlands.Geometric
