import Langlands.Representation.Category.Abelian
import Langlands.Representation.Filtration.MultiplicityStatement
import Mathlib.CategoryTheory.Preadditive.AdditiveFunctor
import Mathlib.Basic.Complex.Basic

/-!
# A multiplicity-one detector identifies simple endpoints

This internal criterion compares an actual irreducible subrepresentation
and an actual irreducible quotient using actual finite-series multiplicities.
-/

namespace Langlands.Classification

open CategoryTheory

universe uG uH uV uW uT

/-- An irreducible subobject and quotient positively detected by a single
functor-image count are isomorphic. -/
def SimpleEndpointMultiplicityOneStatement : Prop :=
  ∀ (G : Type uG) [Group G] [TopologicalSpace G]
    (H : Type uH) [Monoid H]
    (F : SmoothRep.{0, uG, uV} ℂ G ⥤ Rep.{uW} ℂ H)
    [F.Additive] [F.PreservesEpimorphisms] [F.PreservesMonomorphisms]
    (A P Q : SmoothRep.{0, uG, uV} ℂ G),
    P.IsIrreducible → Q.IsIrreducible →
    ∀ (j : P ⟶ A) (q : A ⟶ Q),
    Function.Injective (SmoothRep.hom j) →
    Function.Surjective (SmoothRep.hom q) →
    ∀ (τ : Rep.{uT} ℂ H) (mP mQ : ℕ),
    HasJordanHolderMultiplicity (F.obj A) τ 1 →
    HasJordanHolderMultiplicity (F.obj P) τ mP →
    HasJordanHolderMultiplicity (F.obj Q) τ mQ →
    0 < mP → 0 < mQ →
    Nonempty (P ≅ Q)

end Langlands.Classification
