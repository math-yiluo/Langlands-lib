import Langlands.AlgebraicGeometry.Picard.RelativePicardSheaf
import Mathlib.AlgebraicGeometry.Geometrically.Integral
import Mathlib.AlgebraicGeometry.Morphisms.Flat
import Mathlib.AlgebraicGeometry.Morphisms.Proper
import Mathlib.AlgebraicGeometry.Morphisms.FinitePresentation
import Mathlib.AlgebraicGeometry.Noetherian

/-! # Representability of the Picard class sheaf from noetherian affine tests -/

universe u

open CategoryTheory AlgebraicGeometry

namespace Langlands.AlgebraicGeometry.Picard

/-- Let `R` be a noetherian ring and `f : X ⟶ Spec R` a proper, flat, geometrically integral
morphism with a section. If a scheme `P` locally of finite presentation over `Spec R` has a
functor of points naturally isomorphic to the fppf Picard class sheaf of `f` on all affine
noetherian schemes over `Spec R`, then `P` represents that sheaf on the whole slice
`Over (Spec R)`. -/
def NoetherianAffineTestsPicardExtensionStatement : Prop :=
  ∀ (R : Type u) [CommRing R] [IsNoetherianRing R] (X : Scheme.{u})
    (f : X ⟶ Spec (CommRingCat.of R)),
    IsProper f → Flat f → GeometricallyIntegral f →
    (∃ σ : Spec (CommRingCat.of R) ⟶ X, σ ≫ f = 𝟙 _) →
    ∀ P : Over (Spec (CommRingCat.of R)), LocallyOfFinitePresentation P.hom →
      Nonempty ((ObjectProperty.ι (fun T : Over (Spec (CommRingCat.of R)) =>
            IsAffine T.left ∧ IsNoetherian T.left)).op ⋙
          yoneda.obj P ⋙ uliftFunctor.{u + 1} ≅
        (ObjectProperty.ι (fun T : Over (Spec (CommRingCat.of R)) =>
            IsAffine T.left ∧ IsNoetherian T.left)).op ⋙
          RelativePicard.classSheafPresheaf f) →
      Nonempty ((RelativePicard.classSheafPresheaf f).RepresentableBy P)

end Langlands.AlgebraicGeometry.Picard
