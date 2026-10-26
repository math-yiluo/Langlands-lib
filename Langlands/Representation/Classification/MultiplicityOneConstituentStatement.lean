import Langlands.Representation.Category.Abelian
import Langlands.Representation.Classification.CanonicalConstituents
import Langlands.Representation.Filtration.MultiplicityStatement
import Mathlib.CategoryTheory.Preadditive.AdditiveFunctor

/-!
# Multiplicity-one criteria for strong irreducible constituents

These internal criteria retain actual finite simple-series witnesses and
actual quotient kernels or embedding images.
-/

namespace Langlands.Classification

open CategoryTheory

universe uG uH uV uW uT

/-- A single functor-image count, together with positive detection of every
irreducible quotient and existence of one, forces a strong irreducible head. -/
def MultiplicityOneHeadCriterionStatement : Prop :=
  ∀ (G : Type uG) [Group G] [TopologicalSpace G]
    (H : Type uH) [Monoid H]
    (F : SmoothRep.{0, uG, uV} ℂ G ⥤ Rep.{uW} ℂ H)
    [F.Additive] [F.PreservesEpimorphisms]
    (A : SmoothRep.{0, uG, uV} ℂ G) (τ : Rep.{uT} ℂ H),
    HasJordanHolderMultiplicity (F.obj A) τ 1 →
    (∃ (P : SmoothRep.{0, uG, uV} ℂ G), P.IsIrreducible ∧
      ∃ q : A ⟶ P, Function.Surjective (SmoothRep.hom q)) →
    (∀ (P : SmoothRep.{0, uG, uV} ℂ G), P.IsIrreducible →
      ∀ q : A ⟶ P, Function.Surjective (SmoothRep.hom q) →
        ∃ m : ℕ, HasJordanHolderMultiplicity (F.obj P) τ m ∧ 0 < m) →
    HasIrreducibleHead A.representation

/-- The monomorphism-preserving dual criterion forces equality of all
irreducible embedding images and hence a strong irreducible socle. -/
def MultiplicityOneSocleCriterionStatement : Prop :=
  ∀ (G : Type uG) [Group G] [TopologicalSpace G]
    (H : Type uH) [Monoid H]
    (F : SmoothRep.{0, uG, uV} ℂ G ⥤ Rep.{uW} ℂ H)
    [F.Additive] [F.PreservesMonomorphisms]
    (A : SmoothRep.{0, uG, uV} ℂ G) (τ : Rep.{uT} ℂ H),
    HasJordanHolderMultiplicity (F.obj A) τ 1 →
    (∃ (P : SmoothRep.{0, uG, uV} ℂ G), P.IsIrreducible ∧
      ∃ j : P ⟶ A, Function.Injective (SmoothRep.hom j)) →
    (∀ (P : SmoothRep.{0, uG, uV} ℂ G), P.IsIrreducible →
      ∀ j : P ⟶ A, Function.Injective (SmoothRep.hom j) →
        ∃ m : ℕ, HasJordanHolderMultiplicity (F.obj P) τ m ∧ 0 < m) →
    HasIrreducibleSocle A.representation

/-- The two multiplicity-one constituent criteria, with independent
group, monoid, source, image and test universes. -/
def MultiplicityOneConstituentCriterionStatement : Prop :=
  MultiplicityOneHeadCriterionStatement.{uG, uH, uV, uW, uT} ∧
    MultiplicityOneSocleCriterionStatement.{uG, uH, uV, uW, uT}

end Langlands.Classification
