import Langlands.GroupScheme.Torus.RelativeMultiplicativeType

/-! # Statement: flat square-zero deformations of diagonalizable groups -/

universe u

open CategoryTheory AlgebraicGeometry

namespace Langlands.GroupScheme

open RelativeMultiplicativeType in
/-- An isomorphism from the reduction of a flat affine group of finite presentation
to a diagonalizable group lifts through a square-zero ideal of the base ring.
This is the deformation assertion used in Conrad, *Reductive group schemes* (2014),
the proof of Theorem B.3.2(2), p.289. -/
def DiagonalizableSquareZeroDeformationStatement : Prop :=
  ∀ (R : Type u) [CommRing R] (J : Ideal R), J ^ 2 = ⊥ →
    ∀ (N : Type u) [AddCommGroup N] [AddGroup.FG N]
      (G : GroupScheme (Spec (CommRingCat.of R))) [IsAffineHom G.X.hom]
      [Flat G.X.hom] [LocallyOfFinitePresentation G.X.hom],
      let r := Spec.algebraMap R (R ⧸ J)
      let D := diagonalizable (Spec (CommRingCat.of R)) N
      ∀ f₀ : (GroupScheme.baseChange r).obj G ≅ (GroupScheme.baseChange r).obj D,
        ∃ f : G ≅ D, (GroupScheme.baseChange r).map f.hom = f₀.hom

end Langlands.GroupScheme
