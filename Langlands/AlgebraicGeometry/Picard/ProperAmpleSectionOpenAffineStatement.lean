import Langlands.AlgebraicGeometry.Picard.Ample
import Mathlib.AlgebraicGeometry.Morphisms.Proper

/-! # Generation loci of ample line bundles on proper schemes over affine bases -/

universe u

open CategoryTheory AlgebraicGeometry

namespace Langlands.AlgebraicGeometry.Picard

open Langlands.SchemeModule

/-- On a scheme proper over an affine scheme, the generation locus of every global
section of an ample line bundle is an affine open. -/
def ProperAmpleSectionOpenAffineStatement : Prop :=
  ∀ (X U : Scheme.{u}), IsAffine U → ∀ (f : X ⟶ U), IsProper f →
    ∀ (L : LineBundle X), L.IsAmple → ∀ σ : GlobalSections L.obj,
      IsAffineOpen (trivializationOpen L.obj σ)

end Langlands.AlgebraicGeometry.Picard
