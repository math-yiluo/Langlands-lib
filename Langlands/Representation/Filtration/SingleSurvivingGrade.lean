import Langlands.Representation.Filtration.ZeroFactorDeletionProof
import Langlands.Representation.Filtration.SubsingletonProof
import Langlands.Representation.Filtration.SingletonIso

/-! Objectwise collapse of an actual finite representation filtration. -/

noncomputable section

open CategoryTheory

namespace Langlands

universe uR uG uV uC vC

variable {R : Type uR} [CommRing R] {G : Type uG} [Monoid G]

namespace ObjectRepFiltration

variable {A : Rep.{uV} R G} {n : ℕ}

/-- Retaining one specified occurrence, even if it is zero, gives an actual
isomorphism from the ambient representation to that graded quotient. -/
def singleSurvivingGradeIso (s : ObjectRepFiltration A n) (i₀ : Fin n)
    (hs : ∀ i : Fin n, i ≠ i₀ → Subsingleton (s.gradedRepresentation i)) :
    A ≅ s.gradedRepresentation i₀ := Classical.choice (by
  classical
  let q : {i : Fin n // i = i₀} ≃ Fin 1 :=
    { toFun := fun _ => 0
      invFun := fun _ => ⟨i₀, rfl⟩
      left_inv := fun i => Subtype.ext i.property.symm
      right_inv := fun _ => Subsingleton.elim _ _ }
  obtain ⟨r, e, t, ht⟩ :=
    zeroFactorDeletionTheorem R G A n s (fun i => i = i₀) hs
  have hr : r = 1 := by simpa using Fintype.card_congr (e.trans q)
  subst r
  obtain ⟨f⟩ := ht 0
  exact ⟨((t.lengthOneGradedIso 0).app (Discrete.mk PUnit.unit)).symm ≪≫
    Rep.mkIso f ≪≫ eqToIso (congrArg s.gradedRepresentation (e 0).property)⟩)

end ObjectRepFiltration

namespace RepFunctorFiltration

variable {C : Type uC} [Category.{vC} C] {M : C ⥤ Rep.{uV} R G} {n : ℕ}

/-- Evaluation retains the actual steps and quotient representations. -/
def atObject (s : RepFunctorFiltration M n) (X : C) :
    ObjectRepFiltration (M.obj X) n :=
  ObjectRepFiltration.ofSubrepresentations (fun i => (s.step i).obj X)
    (s.monotone X) (s.zero X) (s.top X)

@[simp]
theorem atObject_gradedRepresentation (s : RepFunctorFiltration M n) (X : C)
    (i : Fin n) : (s.atObject X).gradedRepresentation i = (s.graded i).obj X := rfl

/-- If all actual graded carriers vanish at an input, the ambient carrier vanishes. -/
theorem subsingleton_atObject (s : RepFunctorFiltration M n) (X : C)
    (hs : ∀ i : Fin n, Subsingleton ((s.graded i).obj X)) :
    Subsingleton (M.obj X) :=
  objectRepFiltrationSubsingleton R G (M.obj X) n (s.atObject X) hs

/-- A single possibly nonzero grade determines the whole representation at an input. -/
def singleSurvivingGradeIsoAt (s : RepFunctorFiltration M n) (X : C)
    (i₀ : Fin n)
    (hs : ∀ i : Fin n, i ≠ i₀ → Subsingleton ((s.graded i).obj X)) :
    M.obj X ≅ (s.graded i₀).obj X :=
  (s.atObject X).singleSurvivingGradeIso i₀ hs

end RepFunctorFiltration

end Langlands
