import Langlands.Representation.Filtration.SelectedWeights
import Langlands.Representation.Filtration.SingleSurvivingGrade

/-! Objectwise selection of supplied finite functor filtrations. -/

noncomputable section

open CategoryTheory

namespace Langlands

universe uR uG uA uV uW uC vC

section Equivalence

variable {R : Type uR} [Field R] {G : Type uG} [Group G]
  [TopologicalSpace G] [NonarchimedeanGroup G] [WeaklyLocallyCompactSpace G]
  {A : Type uA} [Group A]
  {V : Type uV} [AddCommGroup V] [Module R V]
  {W : Type uW} [AddCommGroup W] [Module R W]
  {π : Representation R G V} {σ : Representation R G W}
  (ι : A →* G) (hι : ∀ a : A, ι a ∈ Subgroup.center G) (P : (A →* Rˣ) → Prop)

/-- An actual equivalence restricts to the selected sums, without spanning or
admissibility assumptions. Its forward map is the given equivalence. -/
def selectedWeightEquiv (e : π.Equiv σ) :
    (selectedWeightPart π ι hι P).toRepresentation.Equiv
      (selectedWeightPart σ ι hι P).toRepresentation :=
  (selectedWeightMap ι hι P e.toIntertwiningMap).ofBijective ⟨
    fun _ _ h => Subtype.ext (e.injective (congrArg Subtype.val h)),
    fun w => ⟨⟨e.symm w, map_mem_selectedWeightPart ι hι P
      e.symm.toIntertwiningMap w.property⟩,
      Subtype.ext (e.toLinearEquiv.apply_symm_apply w)⟩⟩

@[simp]
theorem selectedWeightEquiv_apply (e : π.Equiv σ)
    (v : selectedWeightPart π ι hι P) :
    (selectedWeightEquiv ι hι P e v : W) = e (v : V) := rfl

end Equivalence

section Evaluation

variable {R : Type uR} [CommRing R] {G : Type uG} [Monoid G]
  {C : Type uC} [Category.{vC} C] {F : C ⥤ Rep.{uV} R G} {n : ℕ}
  {pieces : Fin n → C ⥤ Rep.{uV} R G}

/-- Evaluating a supplied gluing retains its finite list and permutation,
including repeated or zero pieces. -/
theorem IsGluedFrom.exists_objectFiltration (h : IsGluedFrom F pieces) (X : C) :
    ∃ (s : ObjectRepFiltration (F.obj X) n) (e : Equiv.Perm (Fin n)),
      ∀ i, Nonempty ((s.gradedRepresentation i).ρ.Equiv ((pieces (e i)).obj X).ρ) := by
  obtain ⟨e, s, hs⟩ := h
  refine ⟨s.atObject X, e, fun i => ?_⟩
  obtain ⟨f⟩ := hs i
  exact ⟨Representation.equivOfIso (f.app X)⟩

end Evaluation

section Selection

variable {R : Type uR} [Field R] [IsAlgClosed R] {G : Type uG} [Group G]
  [TopologicalSpace G] [NonarchimedeanGroup G] [WeaklyLocallyCompactSpace G]
  {A : Type uA} [Group A]
  {C : Type uC} [Category.{vC} C] {F : C ⥤ Rep.{uV} R G} {n : ℕ}
  {pieces : Fin n → C ⥤ Rep.{uV} R G}

/-- For an admissible value of a supplied gluing, intersecting with its selected
part gives one grade for each selected original piece, in the same permutation. -/
theorem IsGluedFrom.exists_selectedFiltration (h : IsGluedFrom F pieces) (X : C)
    (ι : A →* G) (hι : ∀ a : A, ι a ∈ Subgroup.center G) (P : (A →* Rˣ) → Prop)
    (hX : IsAdmissible (F.obj X).ρ) :
    ∃ (s : ObjectRepFiltration
        (Rep.of (selectedWeightPart (F.obj X).ρ ι hι P).toRepresentation) n)
      (e : Equiv.Perm (Fin n)),
      ∀ i, Nonempty ((s.gradedRepresentation i).ρ.Equiv
        (selectedWeightPart ((pieces (e i)).obj X).ρ ι hι P).toRepresentation) := by
  obtain ⟨s, e, hs⟩ := h.exists_objectFiltration X
  refine ⟨s.selectedFiltration ι hι P, e, fun i => ?_⟩
  obtain ⟨f⟩ := hs i
  exact ⟨(s.selectedGradedEquivOfAdmissible ι hι P hX i).trans
    (selectedWeightEquiv ι hι P f)⟩

end Selection

end Langlands
