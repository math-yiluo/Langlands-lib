import Langlands.Representation.Filtration.QuotientFirstIso

/-! A natural one-step filtration of any representation-valued functor. -/

noncomputable section
open CategoryTheory

namespace Langlands

universe uR uG uV uC vC

variable {R : Type uR} [CommRing R] {G : Type uG} [Monoid G]
  {C : Type uC} [Category.{vC} C]

namespace RepSubfunctor

/-- The actual zero subfunctor. -/
def zero (F : C ⥤ Rep.{uV} R G) : RepSubfunctor F where
  obj _ := ⊥
  map_mem := by
    intro X Y f v hv
    change v = 0 at hv
    change (F.map f).hom v = 0
    rw [hv, map_zero]

/-- The actual full subfunctor. -/
def full (F : C ⥤ Rep.{uV} R G) : RepSubfunctor F where
  obj _ := ⊤
  map_mem := by intros; trivial

/-- The quotient of the full subfunctor by zero is naturally the ambient functor. -/
def zeroQuotientFullIso (F : C ⥤ Rep.{uV} R G) :
    (zero F).quotientFunctor (full F) ≅ F := by
  apply (zero F).quotientNatIsoOfSurjective (full F) (full F).inclusion
  · intro X v
    rfl
  · intro X v
    exact ⟨⟨v, trivial⟩, rfl⟩

end RepSubfunctor

namespace RepFunctorFiltration

/-- The filtration with zero at the first step and the full functor at the last. -/
def oneStep (F : C ⥤ Rep.{uV} R G) : RepFunctorFiltration F 1 where
  step i := if i = 0 then RepSubfunctor.zero F else RepSubfunctor.full F
  monotone X := by
    intro i j hij
    dsimp only
    split_ifs with hi hj hj
    · exact le_rfl
    · exact bot_le
    · have : i = 0 := by simpa [hj] using hij
      exact False.elim (hi this)
    · exact le_rfl
  zero X := rfl
  top X := rfl

/-- The sole actual quotient of `oneStep F` is naturally isomorphic to `F`. -/
def oneStepGradedIso (F : C ⥤ Rep.{uV} R G) (i : Fin 1) :
    (oneStep F).graded i ≅ F := by
  have hi : i = 0 := Subsingleton.elim _ _
  subst i
  exact RepSubfunctor.zeroQuotientFullIso F

end RepFunctorFiltration

/-- A functor is glued from any singleton family naturally isomorphic to it. -/
theorem isGluedFrom_singleton {F : C ⥤ Rep.{uV} R G}
    (pieces : Fin 1 → C ⥤ Rep.{uV} R G) (e : ∀ i, F ≅ pieces i) :
    IsGluedFrom F pieces := by
  refine ⟨Equiv.refl _, RepFunctorFiltration.oneStep F, ?_⟩
  intro i
  exact ⟨(RepFunctorFiltration.oneStepGradedIso F i) ≪≫ e i⟩

/-- The singleton gluing construction with a propositionally singleton length. -/
theorem isGluedFrom_of_length_eq_one {F : C ⥤ Rep.{uV} R G} {n : ℕ}
    (hn : n = 1) (pieces : Fin n → C ⥤ Rep.{uV} R G)
    (e : ∀ i, F ≅ pieces i) : IsGluedFrom F pieces := by
  subst n
  exact isGluedFrom_singleton pieces e

end Langlands
