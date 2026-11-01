import Langlands.Representation.Filtration.OneStep

/-! Empty natural filtrations of functors with zero carriers. -/

open CategoryTheory

namespace Langlands

universe uR uG uV uC vC

variable {R : Type uR} [CommRing R] {G : Type uG} [Monoid G]
  {C : Type uC} [Category.{vC} C]

namespace RepFunctorFiltration

/-- A functor with zero carriers has the actual constant-zero flag of length zero. -/
def zeroLength (F : C ⥤ Rep.{uV} R G) (h : ∀ X, Subsingleton (F.obj X)) :
    RepFunctorFiltration F 0 where
  step _ := RepSubfunctor.zero F
  monotone _ := fun _ _ _ => le_rfl
  zero _ := rfl
  top X := by
    change (⊥ : Subrepresentation (F.obj X).ρ) = ⊤
    apply top_unique
    intro v _
    exact @Subsingleton.elim _ (h X) v 0

/-- The endpoint equations of a length-zero flag force every ambient carrier to vanish. -/
theorem subsingleton_of_zeroLength {F : C ⥤ Rep.{uV} R G}
    (s : RepFunctorFiltration F 0) (X : C) : Subsingleton (F.obj X) := by
  have hbot : (⊥ : Subrepresentation (F.obj X).ρ) = ⊤ :=
    (s.zero X).symm.trans (s.top X)
  have hz (v : F.obj X) : v = 0 := by
    change v ∈ (⊥ : Subrepresentation (F.obj X).ρ)
    rw [hbot]
    trivial
  exact ⟨fun v w => (hz v).trans (hz w).symm⟩

end RepFunctorFiltration

/-- Every empty family is realized by the actual length-zero flag of a zero functor. -/
theorem hasOrderedFiltration_empty {F : C ⥤ Rep.{uV} R G}
    (h : ∀ X, Subsingleton (F.obj X)) (pieces : Fin 0 → C ⥤ Rep.{uV} R G) :
    HasOrderedFiltration F pieces :=
  ⟨RepFunctorFiltration.zeroLength F h, fun i => Fin.elim0 i⟩

/-- A zero functor is glued from the empty family. -/
theorem isGluedFrom_empty {F : C ⥤ Rep.{uV} R G}
    (h : ∀ X, Subsingleton (F.obj X)) (pieces : Fin 0 → C ⥤ Rep.{uV} R G) :
    IsGluedFrom F pieces :=
  ⟨Equiv.refl _, hasOrderedFiltration_empty h _⟩

/-- The empty gluing relation is equivalent to objectwise vanishing. -/
theorem isGluedFrom_empty_iff {F : C ⥤ Rep.{uV} R G}
    (pieces : Fin 0 → C ⥤ Rep.{uV} R G) :
    IsGluedFrom F pieces ↔ ∀ X, Subsingleton (F.obj X) := by
  constructor
  · rintro ⟨_, s, _⟩ X
    exact s.subsingleton_of_zeroLength X
  · intro h
    exact isGluedFrom_empty h pieces

/-- Empty gluing when the supplied family length is propositionally zero. -/
theorem isGluedFrom_of_length_eq_zero {F : C ⥤ Rep.{uV} R G} {n : ℕ}
    (hn : n = 0) (h : ∀ X, Subsingleton (F.obj X))
    (pieces : Fin n → C ⥤ Rep.{uV} R G) : IsGluedFrom F pieces := by
  subst n
  exact isGluedFrom_empty h pieces

end Langlands
