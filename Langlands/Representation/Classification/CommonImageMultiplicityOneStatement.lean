import Langlands.Representation.Category.Abelian
import Langlands.Representation.Classification.CanonicalConstituents
import Langlands.Representation.Filtration.MultiplicityStatement
import Mathlib.CategoryTheory.Preadditive.AdditiveFunctor

/-!
# A common image from positive multiplicity detection

This internal criterion constructs strong endpoints without assuming that
either ambient representation already has a simple endpoint.
-/

namespace Langlands.Classification

open CategoryTheory

universe uG uH uV uW uT

/-- A nonzero map between two single-count objects has an irreducible image
which is the strong head of its source and strong socle of its target, if
every nonzero source quotient and target subobject is detected positively. -/
def CommonImageMultiplicityOneStatement : Prop :=
  ∀ (G : Type uG) [Group G] [TopologicalSpace G]
    (H : Type uH) [Monoid H]
    (F : SmoothRep.{0, uG, uV} ℂ G ⥤ Rep.{uW} ℂ H)
    [F.Additive] [F.PreservesEpimorphisms] [F.PreservesMonomorphisms]
    (A B : SmoothRep.{0, uG, uV} ℂ G) (τ : Rep.{uT} ℂ H),
    HasJordanHolderMultiplicity (F.obj A) τ 1 →
    HasJordanHolderMultiplicity (F.obj B) τ 1 →
    (∀ (P : SmoothRep.{0, uG, uV} ℂ G) (q : A ⟶ P),
      Function.Surjective (SmoothRep.hom q) → q ≠ 0 →
        ∃ m : ℕ, HasJordanHolderMultiplicity (F.obj P) τ m ∧ 0 < m) →
    (∀ (P : SmoothRep.{0, uG, uV} ℂ G) (j : P ⟶ B),
      Function.Injective (SmoothRep.hom j) → j ≠ 0 →
        ∃ m : ℕ, HasJordanHolderMultiplicity (F.obj P) τ m ∧ 0 < m) →
    ∀ (f : A ⟶ B), f ≠ 0 →
      ∃ (P : SmoothRep.{0, uG, uV} ℂ G) (q : A ⟶ P) (j : P ⟶ B),
        Function.Surjective (SmoothRep.hom q) ∧
        Function.Injective (SmoothRep.hom j) ∧ f = q ≫ j ∧
        IsIrreducibleHead A.representation P.representation ∧
        IsIrreducibleSocle B.representation P.representation

end Langlands.Classification
