import Langlands.AlgebraicGeometry.SectionComponent
import Mathlib.AlgebraicGeometry.Geometrically.Reduced
import Mathlib.AlgebraicGeometry.Morphisms.FinitePresentation
import Mathlib.AlgebraicGeometry.Morphisms.QuasiSeparated

/-! # Openness of fibre components meeting a section -/

universe u

open CategoryTheory AlgebraicGeometry

namespace Langlands.AlgebraicGeometry.SectionComponent

/-- For a flat morphism of finite presentation with geometrically reduced fibres,
the union of the fibre components meeting a section is open. -/
def FlatFinitePresentationOpennessStatement : Prop :=
  ∀ (X Y : Scheme.{u}) (f : X ⟶ Y) (e : Y ⟶ X) (he : e ≫ f = 𝟙 Y),
    Flat f → LocallyOfFinitePresentation f → QuasiCompact f → QuasiSeparated f →
      GeometricallyReduced f → IsOpen (componentSet f e he)

end Langlands.AlgebraicGeometry.SectionComponent
