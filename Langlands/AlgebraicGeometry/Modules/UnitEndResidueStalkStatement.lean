import Langlands.AlgebraicGeometry.Modules.SectionResidue

/-! # Scalar residue criterion for structure-module endomorphisms -/

universe u

open CategoryTheory AlgebraicGeometry

namespace Langlands.SchemeModule

/-- An endomorphism of the structure module is invertible on the underlying
abelian-group stalk exactly when its value at one has nonzero residue. -/
def UnitEndResidueStalkCriterion : Prop :=
  ∀ (X : Scheme.{u}) (φ : structureModule X ⟶ structureModule X) (x : X),
    IsIso ((TopCat.Presheaf.stalkFunctor Ab.{u} x).map φ.mapPresheaf) ↔
      X.Γevaluation x (φ.app ⊤ (1 : Γ(X, ⊤))) ≠ 0

end Langlands.SchemeModule
