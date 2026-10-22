import Langlands.Representation.Filtration.ZeroFactorDeletionStatement

/-! Proof that prescribed zero factors can be deleted from an actual representation filtration. -/

open CategoryTheory

namespace Langlands.ObjectRepFiltration

universe uR uG uV uL

/-- Selected indices of `Fin (m + 1)` when the initial index is not selected. -/
def succSelectedEquiv {m : ℕ} {P : Fin (m + 1) → Prop} (h0 : ¬ P 0) :
    {i : Fin m // P i.succ} ≃ {i : Fin (m + 1) // P i} where
  toFun x := ⟨x.val.succ, x.property⟩
  invFun y := ⟨y.val.pred (fun hy => h0 (hy ▸ y.property)), by simpa using y.property⟩
  left_inv x := Subtype.ext (by simp)
  right_inv y := Subtype.ext (by simp)

/-- Selected indices of `Fin (m + 1)` when the initial index is selected, listed
with the initial index first and the remaining ones in the order given by `e`. -/
def consSelectedEquiv {m r : ℕ} {P : Fin (m + 1) → Prop} (h0 : P 0)
    (e : Fin r ≃ {i : Fin m // P i.succ}) : Fin (r + 1) ≃ {i : Fin (m + 1) // P i} where
  toFun := Fin.cases ⟨0, h0⟩ (fun k => ⟨(e k).val.succ, (e k).property⟩)
  invFun y := if hy : y.val = 0 then 0 else
    (e.symm ⟨y.val.pred hy, by simpa using y.property⟩).succ
  left_inv j := by
    cases j using Fin.cases with
    | zero => simp
    | succ k => simp [Fin.succ_ne_zero]
  right_inv y := by
    obtain ⟨y, hy⟩ := y
    cases y using Fin.cases with
    | zero => simp
    | succ i => simp [Fin.succ_ne_zero]

/-- A chain whose unselected steps are equalities can be shortened to the selected
steps. The new chain has the same endpoints, and its `j`th step is the step of the
original chain at the selected index `e j`. -/
theorem exists_chain_deletion {L : Type uL} :
    ∀ (m : ℕ) (f : Fin (m + 1) → L) (P : Fin m → Prop),
      (∀ i : Fin m, ¬ P i → f i.castSucc = f i.succ) →
        ∃ (r : ℕ) (e : Fin r ≃ {i : Fin m // P i}) (g : Fin (r + 1) → L),
          g 0 = f 0 ∧ g (Fin.last r) = f (Fin.last m) ∧
            ∀ j : Fin r, g j.castSucc = f (e j).val.castSucc ∧ g j.succ = f (e j).val.succ
  | 0, f, P, _ => ⟨0, Equiv.equivOfIsEmpty _ _, f, rfl, rfl, fun j => j.elim0⟩
  | m + 1, f, P, hf => by
    obtain ⟨r, e, g, hg0, hglast, hg⟩ :=
      exists_chain_deletion m (Fin.tail f) (fun i => P i.succ) (fun i hi => hf i.succ hi)
    by_cases h0 : P 0
    · refine ⟨r + 1, consSelectedEquiv h0 e, Fin.cons (f 0) g, rfl, ?_, fun j => ?_⟩
      · exact hglast
      · cases j using Fin.cases with
        | zero => exact ⟨rfl, hg0⟩
        | succ k => exact hg k
    · refine ⟨r, e.trans (succSelectedEquiv h0), g, ?_, ?_, fun j => ?_⟩
      · exact hg0.trans (hf 0 h0).symm
      · exact hglast
      · exact hg j

variable {R : Type uR} [CommRing R] {G : Type uG} [Monoid G] {A : Rep.{uV} R G}

/-- A zero graded quotient forces its two adjacent invariant subspaces to coincide. -/
theorem subrepresentation_castSucc_eq_succ {n : ℕ} (s : ObjectRepFiltration A n) (i : Fin n)
    (h : Subsingleton (s.gradedRepresentation i)) :
    s.subrepresentation i.castSucc = s.subrepresentation i.succ := by
  refine le_antisymm (s.monotone_subrepresentation (Fin.castSucc_le_succ i)) ?_
  have h' : Subsingleton ((s.subrepresentation i.succ).toSubmodule ⧸
      (s.subrepresentation i.castSucc).toSubmodule.comap
        (s.subrepresentation i.succ).toSubmodule.subtype) := h
  rw [Submodule.Quotient.subsingleton_iff, Submodule.comap_subtype_eq_top] at h'
  exact h'

/-- The actual quotient of one invariant subspace by another, built exactly as the
graded quotients of `ObjectRepFiltration`. -/
abbrev stepQuotient (S T : Subrepresentation A.ρ) : Rep.{uV} R G :=
  (objectRepresentationSubfunctor A S).quotientObj (objectRepresentationSubfunctor A T)
    (Discrete.mk PUnit.unit)

/-- Graded quotients with the same lower and upper invariant subspaces are equivalent
representations. -/
theorem nonempty_equiv_gradedRepresentation {n k : ℕ} (t : ObjectRepFiltration A k)
    (s : ObjectRepFiltration A n) (j : Fin k) (i : Fin n)
    (h₀ : t.subrepresentation j.castSucc = s.subrepresentation i.castSucc)
    (h₁ : t.subrepresentation j.succ = s.subrepresentation i.succ) :
    Nonempty (Representation.Equiv (t.gradedRepresentation j).ρ
      (s.gradedRepresentation i).ρ) := by
  change Nonempty (Representation.Equiv
    (stepQuotient (t.subrepresentation j.castSucc) (t.subrepresentation j.succ)).ρ
    (stepQuotient (s.subrepresentation i.castSucc) (s.subrepresentation i.succ)).ρ)
  rw [h₀, h₁]
  exact ⟨Representation.Equiv.refl _⟩

/-- Prescribed zero factors can be deleted from an actual representation filtration,
retaining every selected index exactly once. -/
theorem zeroFactorDeletionTheorem : ZeroFactorDeletionTheorem.{uR, uG, uV} := by
  intro R _ G _ A m s P hP
  obtain ⟨r, e, g, hg0, hglast, hg⟩ := exists_chain_deletion m s.subrepresentation P
    (fun i hi => subrepresentation_castSucc_eq_succ s i (hP i hi))
  have hmono : Monotone g := by
    refine Fin.monotone_iff_le_succ.mpr fun j => ?_
    rw [(hg j).1, (hg j).2]
    exact s.monotone_subrepresentation (Fin.castSucc_le_succ _)
  refine ⟨r, e, ofSubrepresentations g hmono (by rw [hg0]; exact s.subrepresentation_zero)
    (by rw [hglast]; exact s.subrepresentation_last), fun j => ?_⟩
  exact nonempty_equiv_gradedRepresentation _ s j (e j).val (hg j).1 (hg j).2

end Langlands.ObjectRepFiltration
