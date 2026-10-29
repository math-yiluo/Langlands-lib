import Langlands.Representation.Category.Abelian
import Langlands.Representation.Classification.CanonicalConstituents
import Langlands.Representation.Filtration.MultiplicityStatement
import Mathlib.CategoryTheory.Preadditive.AdditiveFunctor

/-!
# Strong irreducible heads from a positive total count

The criterion retains actual finite simple-series counts, quotient maps and
quotient kernels.
-/

namespace Langlands.Classification

open CategoryTheory

universe uG uH uV uW uT

/-- A positive total functor-image count, an actual irreducible quotient, and
an equally large count in every irreducible quotient image force a strong
irreducible head. -/
def PositiveTotalHeadCriterionStatement : Prop :=
  ∀ (G : Type uG) [Group G] [TopologicalSpace G]
    (H : Type uH) [Monoid H]
    (F : SmoothRep.{0, uG, uV} ℂ G ⥤ Rep.{uW} ℂ H)
    [F.Additive] [F.PreservesEpimorphisms]
    (A : SmoothRep.{0, uG, uV} ℂ G) (τ : Rep.{uT} ℂ H) (m : ℕ),
    0 < m →
    HasJordanHolderMultiplicity (F.obj A) τ m →
    (∃ (P : SmoothRep.{0, uG, uV} ℂ G), P.IsIrreducible ∧
      ∃ q : A ⟶ P, Function.Surjective (SmoothRep.hom q)) →
    (∀ (P : SmoothRep.{0, uG, uV} ℂ G), P.IsIrreducible →
      ∀ q : A ⟶ P, Function.Surjective (SmoothRep.hom q) →
        ∃ c : ℕ, HasJordanHolderMultiplicity (F.obj P) τ c ∧ m ≤ c) →
    HasIrreducibleHead A.representation

end Langlands.Classification
