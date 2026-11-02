import Langlands.Representation.Filtration.QuotientFirstIso

/-! Extracting an actual natural isomorphism from a singleton filtration. -/

noncomputable section

open CategoryTheory

namespace Langlands

universe uR uG uV uC vC

variable {R : Type uR} [CommRing R] {G : Type uG} [Monoid G]
  {C : Type uC} [Category.{vC} C] {M : C ⥤ Rep.{uV} R G}

/-- The only grade of an arbitrary length-one filtration is the original functor.
Adapted from Worker 168's `AdjacentQuotientUpperProduct.oneStepGradedIso`. -/
def RepFunctorFiltration.lengthOneGradedIso (s : RepFunctorFiltration M 1)
    (i : Fin 1) : s.graded i ≅ M := by
  have hi : i = 0 := Subsingleton.elim _ _
  subst i
  apply (s.step 0).quotientNatIsoOfSurjective (s.step 1) (s.step 1).inclusion
  · intro X v
    change (v : M.obj X) ∈ (s.step 0).obj X ↔ (v : M.obj X) = 0
    rw [s.zero X]
    rfl
  · intro X v
    refine ⟨⟨v, ?_⟩, rfl⟩
    rw [show (s.step 1).obj X = ⊤ from s.top X]
    trivial

/-- Choose a natural isomorphism from gluing with exactly one supplied piece. -/
def IsGluedFrom.isoOfLengthOne {n : ℕ} {P : Fin n → C ⥤ Rep.{uV} R G}
    (h : IsGluedFrom M P) (hn : n = 1) (i : Fin n) : M ≅ P i :=
  Classical.choice (by
    subst n
    obtain ⟨e, s, hs⟩ := h
    obtain ⟨a⟩ := hs 0
    exact ⟨(s.lengthOneGradedIso 0).symm ≪≫ a ≪≫
      eqToIso (congrArg P (Subsingleton.elim _ _))⟩)

end Langlands
