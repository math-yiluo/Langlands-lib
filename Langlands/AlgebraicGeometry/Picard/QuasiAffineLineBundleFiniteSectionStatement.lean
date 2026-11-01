import Langlands.AlgebraicGeometry.Picard.LineBundle
import Langlands.AlgebraicGeometry.Modules.SectionLocus
import Mathlib.AlgebraicGeometry.QuasiAffine

/-! # Sections of a quasi-affine line bundle avoiding finitely many points -/

universe u

open AlgebraicGeometry

namespace Langlands.AlgebraicGeometry.Picard

/-- Every finite set on a quasi-affine scheme lies in the generation open of a
global section of any line bundle. This is a proposition, not a chosen section. -/
def QuasiAffineLineBundleFiniteSectionStatement : Prop :=
  ∀ (X : Scheme.{u}) [Scheme.IsQuasiAffine X] (L : LineBundle X)
    (E : Set X), E.Finite →
      ∃ s : Langlands.SchemeModule.GlobalSections L.obj,
        E ⊆ (Langlands.SchemeModule.trivializationOpen L.obj s : Set X)

end Langlands.AlgebraicGeometry.Picard
