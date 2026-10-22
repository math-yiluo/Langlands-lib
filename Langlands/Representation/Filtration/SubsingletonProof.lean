import Langlands.Representation.Filtration.VanishingStatement

/-! A finite filtration with zero graded quotients has zero ambient module. -/

namespace Langlands

universe uR uG uV

namespace ObjectRepFiltration

variable {R : Type uR} {G : Type uG} [CommRing R] [Monoid G]
  {A : Rep.{uV} R G} {n : ℕ}

/-- A vector of the upper step has zero class in the actual graded quotient
exactly when it lies in the lower step. -/
theorem gradedProjection_eq_zero_iff (s : ObjectRepFiltration A n) (i : Fin n)
    (v : (s.subrepresentation i.succ).toSubmodule) :
    (s.gradedProjection i).hom v = 0 ↔ (v : A) ∈ s.subrepresentation i.castSucc := by
  exact Submodule.Quotient.mk_eq_zero _

/-- A zero graded quotient forces two consecutive steps to agree. -/
theorem subrepresentation_succ_le_of_subsingleton (s : ObjectRepFiltration A n)
    (i : Fin n) [Subsingleton (s.gradedRepresentation i)] :
    s.subrepresentation i.succ ≤ s.subrepresentation i.castSucc := fun v hv =>
  (s.gradedProjection_eq_zero_iff i ⟨v, hv⟩).mp (Subsingleton.elim _ _)

/-- If every graded quotient is zero, every step is the whole representation. -/
theorem subrepresentation_eq_top_of_subsingleton (s : ObjectRepFiltration A n)
    (hs : ∀ i : Fin n, Subsingleton (s.gradedRepresentation i)) (k : Fin (n + 1)) :
    s.subrepresentation k = ⊤ := by
  induction k using Fin.reverseInduction with
  | last => exact s.subrepresentation_last
  | cast i ih =>
    have := hs i
    exact top_le_iff.mp (ih.ge.trans (s.subrepresentation_succ_le_of_subsingleton i))

end ObjectRepFiltration

/-- Proof of `ObjectRepFiltrationSubsingletonStatement`. -/
theorem objectRepFiltrationSubsingleton :
    ObjectRepFiltrationSubsingletonStatement.{uR, uG, uV} := by
  intro R _ G _ A r s hs
  have h0 := s.subrepresentation_eq_top_of_subsingleton hs 0
  rw [s.subrepresentation_zero] at h0
  refine ⟨fun v w => ?_⟩
  have hmem : ∀ x : A, x = 0 := fun x => by
    have hx : x ∈ (⊤ : Subrepresentation A.ρ) := Submodule.mem_top (R := R) (x := x)
    rw [← h0] at hx
    exact (Submodule.mem_bot R).mp hx
  rw [hmem v, hmem w]

end Langlands
