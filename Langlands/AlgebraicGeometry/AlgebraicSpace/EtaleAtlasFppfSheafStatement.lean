import Langlands.AlgebraicGeometry.AlgebraicSpace.Basic
import Mathlib.AlgebraicGeometry.Sites.Etale

/-! # Fppf descent for an etale sheaf with an etale scheme atlas -/

universe u

open CategoryTheory AlgebraicGeometry

namespace Langlands.AlgebraicGeometry.AlgebraicSpace

/-- An actual etale sheaf with representable diagonal and a geometrically
surjective etale scheme atlas is a sheaf for the full fppf topology. -/
def EtaleAtlasFppfSheafStatement : Prop :=
  ∀ (S : Scheme.{u}) (F : Presheaf S),
    CategoryTheory.Presheaf.IsSheaf (Scheme.etaleTopology.over S) F →
    HasRepresentableDiagonal F →
    (∃ (U : Over S) (a : (schemeYoneda S).obj U ⟶ F),
      IsEtale a ∧ IsSurjective a) →
    CategoryTheory.Presheaf.IsSheaf (fppfTopology S) F

end Langlands.AlgebraicGeometry.AlgebraicSpace
