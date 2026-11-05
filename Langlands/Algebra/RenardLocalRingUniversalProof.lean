import Langlands.Algebra.RenardLocalRingUniversalStatement

/-! # The categorical universal property of the actual ring localization -/

set_option autoImplicit false

noncomputable section

open CategoryTheory

namespace Langlands.Renard.RingLocalization

universe u

/-- The actual chosen factor satisfies the canonical triangle equation. -/
theorem categoricalFactorizationStatement :
    CategoricalFactorizationStatement.{u} := by
  intro A N f
  apply Hom.ext
  apply RingHom.ext
  intro a
  exact canonicalFactor_algebraMap A N f a

/-- Every commuting map in the actual local full subcategory is the chosen factor. -/
theorem categoricalFactorUniquenessStatement :
    CategoricalFactorUniquenessStatement.{u} := by
  intro A N f g hg
  apply ObjectProperty.hom_ext
  apply Hom.ext
  apply IsLocalization.ringHom_ext (S := Localization A.denominators) A.denominators
  apply RingHom.ext
  intro a
  change g.hom.raw (algebraMap A.ring (Localization A.denominators) a) =
    (canonicalFactor A N f).hom.raw
      (algebraMap A.ring (Localization A.denominators) a)
  rw [canonicalFactor_algebraMap]
  exact congrArg (fun k : A ⟶ N.obj => k.raw a) hg

/-- Unique actual factors give initiality of the actual canonical structured arrow. -/
theorem categoricalInitialityStatement :
    CategoricalInitialityStatement.{u} := by
  intro A
  refine ⟨Limits.IsInitial.ofUniqueHom ?_ ?_⟩
  · intro B
    exact StructuredArrow.homMk (canonicalFactor A B.right B.hom)
      (categoricalFactorizationStatement A B.right B.hom)
  · intro B g
    apply StructuredArrow.hom_ext
    exact categoricalFactorUniquenessStatement
      A B.right B.hom g.right (StructuredArrow.w g)

/-- The exact published ring-localization categorical universality aggregate. -/
theorem categoricalUniversalStatements :
    CategoricalUniversalStatements.{u} :=
  ⟨categoricalFactorizationStatement,
    categoricalFactorUniquenessStatement,
    categoricalInitialityStatement⟩

end Langlands.Renard.RingLocalization
