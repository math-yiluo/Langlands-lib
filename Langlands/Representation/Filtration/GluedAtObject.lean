import Langlands.Representation.Filtration.SingleSurvivingGrade

/-! # Selected factors of a glued filtration at an object -/

noncomputable section

open CategoryTheory

namespace Langlands

universe uR uG uV uC vC

variable {R : Type uR} [CommRing R] {G : Type uG} [Monoid G]
  {C : Type uC} [Category.{vC} C]
  {F : C ⥤ Rep.{uV} R G} {n : ℕ}
  {pieces : Fin n → C ⥤ Rep.{uV} R G}

/-- Evaluate a glued filtration and delete any specified vanishing factors.
Each selected original index occurs exactly once, regardless of the
permutation in the gluing relation or whether its factor also vanishes. -/
theorem IsGluedFrom.exists_selected_filtration
    (h : IsGluedFrom F pieces) (X : C) (P : Fin n → Prop)
    (hzero : ∀ i, ¬ P i → Subsingleton ((pieces i).obj X)) :
    ∃ (r : ℕ) (e : Fin r ≃ {i : Fin n // P i})
      (s : ObjectRepFiltration (F.obj X) r),
      ∀ j, Nonempty ((s.gradedRepresentation j).ρ.Equiv
        ((pieces (e j).val).obj X).ρ) := by
  classical
  obtain ⟨perm, s, hs⟩ := h
  have hvanish (i : Fin n) (hi : ¬ P (perm i)) :
      Subsingleton ((s.atObject X).gradedRepresentation i) := by
    let E := Representation.equivOfIso ((Classical.choice (hs i)).app X)
    exact ⟨fun a b => E.injective
      (@Subsingleton.elim ((pieces (perm i)).obj X) (hzero (perm i) hi) _ _)⟩
  obtain ⟨r, e, t, ht⟩ :=
    ObjectRepFiltration.zeroFactorDeletionTheorem R G (F.obj X) n
      (s.atObject X) (fun i => P (perm i)) hvanish
  let reindex : {i : Fin n // P (perm i)} ≃ {i : Fin n // P i} :=
    { toFun := fun i => ⟨perm i.val, i.property⟩
      invFun := fun i => ⟨perm.symm i.val, by simpa using i.property⟩
      left_inv := fun i => Subtype.ext (perm.symm_apply_apply i.val)
      right_inv := fun i => Subtype.ext (perm.apply_symm_apply i.val) }
  refine ⟨r, e.trans reindex, t, ?_⟩
  intro j
  obtain ⟨E⟩ := ht j
  exact ⟨E.trans (Representation.equivOfIso
    ((Classical.choice (hs (e j).val)).app X))⟩

/-- A chosen filtration enumerating precisely the selected original factors. -/
def IsGluedFrom.selectedFiltration
    (h : IsGluedFrom F pieces) (X : C) (P : Fin n → Prop)
    (hzero : ∀ i, ¬ P i → Subsingleton ((pieces i).obj X)) :
    Σ (r : ℕ) (e : Fin r ≃ {i : Fin n // P i}),
      {s : ObjectRepFiltration (F.obj X) r //
        ∀ j, Nonempty ((s.gradedRepresentation j).ρ.Equiv
          ((pieces (e j).val).obj X).ρ)} :=
  Classical.choice (by
    obtain ⟨r, e, s, hs⟩ := h.exists_selected_filtration X P hzero
    exact ⟨⟨r, e, s, hs⟩⟩)

end Langlands
