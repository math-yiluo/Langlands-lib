import Mathlib.AlgebraicGeometry.Morphisms.FinitePresentation
import Mathlib.AlgebraicGeometry.Morphisms.QuasiSeparated

/-! # Initial finitely presented scheme models over filtered ring colimits -/

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

namespace Langlands.AlgebraicGeometry.SchemeLimitModel

/-- Every finitely presented scheme over a filtered colimit of rings is the
base change of a finitely presented scheme over one of the actual stages. -/
def SchemeFilteredModelExistence : Prop :=
  ∀ (J : Type u) [SmallCategory J] [IsFiltered J]
    (F : J ⥤ CommRingCat.{u}) (c : Cocone F) (_hc : IsColimit c)
    (X : Scheme.{u}) (g : X ⟶ Spec c.pt)
    [QuasiCompact g] [QuasiSeparated g] [LocallyOfFinitePresentation g],
    ∃ (j : J) (Xj : Scheme.{u}) (gj : Xj ⟶ Spec (F.obj j)) (π : X ⟶ Xj),
      LocallyOfFinitePresentation gj ∧ QuasiCompact gj ∧ QuasiSeparated gj ∧
        IsPullback π g gj (Spec.map (c.ι.app j))

end Langlands.AlgebraicGeometry.SchemeLimitModel
