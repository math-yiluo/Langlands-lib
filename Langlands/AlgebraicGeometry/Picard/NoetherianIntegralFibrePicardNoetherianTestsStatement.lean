import Langlands.AlgebraicGeometry.Picard.NoetherianIntegralFibrePicardSheafAFSchemeStatement
import Mathlib.AlgebraicGeometry.Morphisms.FinitePresentation
import Mathlib.AlgebraicGeometry.Noetherian

/-! # Picard sheaf of a pointed projective flat family with geometrically integral fibres on
noetherian affine test schemes -/

universe u

open CategoryTheory AlgebraicGeometry

namespace Langlands.AlgebraicGeometry.Picard

/-- The inclusion of the full subcategory of schemes over `S` whose source is affine and
noetherian. -/
abbrev noetherianAffineOverι (S : Scheme.{u}) :=
  ObjectProperty.ι (fun T : Over S => IsAffine T.left ∧ IsNoetherian T.left)

/-- For every noetherian ring `R` and every proper flat morphism `f : X ⟶ Spec R` with
geometrically integral fibres and a section, such that `X` has an ample line bundle, there is a
scheme `P` locally of finite presentation over `Spec R`, in which every finite set of points lies
in an affine open subscheme, whose functor of points agrees naturally with the fppf Picard class
sheaf of `f` on all affine noetherian schemes over `Spec R`. -/
def NoetherianIntegralFibrePicardNoetherianTestsStatement : Prop :=
  ∀ (R : Type u) [CommRing R] [IsNoetherianRing R] (X : Scheme.{u})
    (f : X ⟶ Spec (CommRingCat.of R)),
    IsProper f → Flat f → GeometricallyIntegral f →
    (∃ σ : Spec (CommRingCat.of R) ⟶ X, σ ≫ f = 𝟙 _) →
    (∃ L : LineBundle X, L.IsAmple) →
      ∃ P : Over (Spec (CommRingCat.of R)),
        LocallyOfFinitePresentation P.hom ∧
          PointTopology.HasFiniteAffineNeighborhoods P.left ∧
            Nonempty ((noetherianAffineOverι (Spec (CommRingCat.of R))).op ⋙
                yoneda.obj P ⋙ uliftFunctor.{u + 1} ≅
              (noetherianAffineOverι (Spec (CommRingCat.of R))).op ⋙
                RelativePicard.classSheafPresheaf f)

end Langlands.AlgebraicGeometry.Picard
