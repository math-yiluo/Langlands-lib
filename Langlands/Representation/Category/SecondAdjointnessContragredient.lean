import Langlands.Representation.Category.FrobeniusChainAdjunction
import Mathlib.CategoryTheory.Adjunction.Unique

/-!
# The contragredient formula from second adjointness

Renard 2026, VI.9.6, the implication (VI.9.6.1) ⇒ (VI.9.6.2), obtained by uniqueness
of right adjoints applied to the Hom chain (VI.9.6.3).
-/

noncomputable section

open CategoryTheory

namespace Langlands.SmoothRep

universe uG uV uM uW

variable {G : Type uG} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
  {M : Type uM} [Group M] [TopologicalSpace M] [IsTopologicalGroup M]
  {L : SmoothRep.{0, uM, uW} ℂ M ⥤ SmoothRep.{0, uG, uV} ℂ G}
  {R r : SmoothRep.{0, uG, uV} ℂ G ⥤ SmoothRep.{0, uM, uW} ℂ M}

/-- Second adjointness and Frobenius reciprocity imply the contragredient formula,
provided induction commutes naturally with the smooth contragredient. -/
def contragredientIsoOfSecondAdjunction (F : r ⊣ L)
    (C : L.op ⋙ contragredientFunctor.{0, uG, uV} ≅
      contragredientFunctor.{0, uM, uW} ⋙ L) (A : L ⊣ R) :
    contragredientFunctor.{0, uG, uV} ⋙ R ≅
      r.op ⋙ contragredientFunctor.{0, uM, uW} :=
  (A.comp contragredientAdjunction.{0, uG, uV}).rightAdjointUniq
    ((contragredientAdjunction.{0, uM, uW}.comp F.op).ofNatIsoLeft
      (contragredientRightOpIso C))

/-- The forward implication of Renard VI.9.6, expressed without choosing an adjunction. -/
theorem nonempty_contragredientIso_of_secondAdjunction (F : r ⊣ L)
    (C : L.op ⋙ contragredientFunctor.{0, uG, uV} ≅
      contragredientFunctor.{0, uM, uW} ⋙ L) (hA : Nonempty (L ⊣ R)) :
    Nonempty (contragredientFunctor.{0, uG, uV} ⋙ R ≅
      r.op ⋙ contragredientFunctor.{0, uM, uW}) := by
  obtain ⟨A⟩ := hA
  exact ⟨contragredientIsoOfSecondAdjunction F C A⟩

end Langlands.SmoothRep
