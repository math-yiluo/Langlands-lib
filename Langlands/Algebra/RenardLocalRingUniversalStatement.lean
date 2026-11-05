import Langlands.Algebra.RenardLocalRingCategory

/-! # The actual categorical universal property of ring localization -/

set_option autoImplicit false

open CategoryTheory

namespace Langlands.Renard.RingLocalization

universe u

/-- The actual constructed factor satisfies the right universal-arrow equation. -/
def CategoricalFactorizationStatement : Prop :=
  ∀ (A : RingPair.{u}) (N : LocalRingCat.{u}) (f : A ⟶ N.obj),
    canonicalRingMap A ≫ localRingInclusion.map (canonicalFactor A N f) = f

/-- Any actual local-category factor satisfying the canonical equation equals
the constructed factor. -/
def CategoricalFactorUniquenessStatement : Prop :=
  ∀ (A : RingPair.{u}) (N : LocalRingCat.{u}) (f : A ⟶ N.obj)
    (g : canonicalLocalObject A ⟶ N),
    canonicalRingMap A ≫ localRingInclusion.map g = f →
      g = canonicalFactor A N f

/-- Initiality of the actual canonical structured arrow, expressed as a proposition. -/
def CategoricalInitialityStatement : Prop :=
  ∀ A : RingPair.{u},
    Nonempty (StructuredArrow.IsUniversal (canonicalStructuredArrow A))

/-- Closed factorization, uniqueness and initiality assertions for actual
ring-denominator pairs and their actual localization. -/
def CategoricalUniversalStatements : Prop :=
  CategoricalFactorizationStatement.{u} ∧
    CategoricalFactorUniquenessStatement.{u} ∧
    CategoricalInitialityStatement.{u}

end Langlands.Renard.RingLocalization
