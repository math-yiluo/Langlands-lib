import Mathlib.AlgebraicGeometry.AffineScheme
import Langlands.AlgebraicGeometry.Picard.LineBundle
import Langlands.AlgebraicGeometry.Modules.SectionLocus

/-! # Affineness of an affine open intersected with a line-bundle section locus -/

universe u

open AlgebraicGeometry

namespace Langlands.AlgebraicGeometry.Picard

/-- Intersecting an affine open with the whole generation locus of a line-bundle
section gives an affine open. -/
def AffineGenerationLocusIntersectionStatement : Prop :=
  ∀ (X : Scheme.{u}) (L : LineBundle X)
    (s : Langlands.SchemeModule.GlobalSections L.obj) (U : X.Opens),
    IsAffineOpen U →
      IsAffineOpen (U ⊓ Langlands.SchemeModule.trivializationOpen L.obj s)

end Langlands.AlgebraicGeometry.Picard
