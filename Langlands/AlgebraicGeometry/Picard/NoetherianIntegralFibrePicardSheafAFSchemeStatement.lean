import Langlands.AlgebraicGeometry.Picard.Ample
import Langlands.AlgebraicGeometry.Picard.RelativePicardSheaf
import Langlands.AlgebraicGeometry.PointTopology.AffineChartWeilRestrictionRepresentability
import Mathlib.AlgebraicGeometry.Geometrically.Integral
import Mathlib.AlgebraicGeometry.Morphisms.Flat
import Mathlib.AlgebraicGeometry.Morphisms.Proper

/-! # Picard sheaf of a pointed projective flat family with geometrically integral fibres over a
noetherian affine base -/

universe u

open CategoryTheory AlgebraicGeometry

namespace Langlands.AlgebraicGeometry.Picard

/-- For every noetherian ring `R` and every proper flat morphism `f : X ⟶ Spec R` with
geometrically integral fibres and a section, such that `X` has an ample line bundle, the actual
fppf Picard class sheaf of `f` is represented by a scheme `P` over `Spec R` in which every finite
set of points lies in an affine open subscheme. -/
def NoetherianIntegralFibrePicardSheafAFSchemeStatement : Prop :=
  ∀ (R : Type u) [CommRing R] [IsNoetherianRing R] (X : Scheme.{u})
    (f : X ⟶ Spec (CommRingCat.of R)),
    IsProper f → Flat f → GeometricallyIntegral f →
    (∃ σ : Spec (CommRingCat.of R) ⟶ X, σ ≫ f = 𝟙 _) →
    (∃ L : LineBundle X, L.IsAmple) →
      ∃ P : Over (Spec (CommRingCat.of R)),
        PointTopology.HasFiniteAffineNeighborhoods P.left ∧
          Nonempty ((RelativePicard.classSheafPresheaf f).RepresentableBy P)

end Langlands.AlgebraicGeometry.Picard
