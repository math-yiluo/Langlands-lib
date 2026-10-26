import Langlands.AlgebraicGeometry.Modules.SectionResidue
import Langlands.AlgebraicGeometry.Picard.LineBundle

/-! # Whole generation opens and actual pullback of line-bundle sections -/

universe u

open CategoryTheory AlgebraicGeometry Langlands.AlgebraicGeometry.Picard

namespace Langlands.SchemeModule

/-- The whole generation open of an actually pulled-back line-bundle section
is the inverse image of its original whole generation open. -/
def LineBundlePullbackSectionOpenStatement : Prop :=
  ∀ (X Y : Scheme.{u}) (f : Y ⟶ X) (L : LineBundle X)
      (s : GlobalSections L.obj),
    trivializationOpen ((Scheme.Modules.pullback f).obj L.obj)
        (pullbackSection f L.obj s) =
      f ⁻¹ᵁ (trivializationOpen L.obj s)

end Langlands.SchemeModule
