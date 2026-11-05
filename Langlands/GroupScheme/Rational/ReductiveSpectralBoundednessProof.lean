import Langlands.GroupScheme.Rational.DenseSpectralBoundedness
import Langlands.GroupScheme.Rational.LocalFieldDensity
import Langlands.GroupScheme.IntegralModel
import Langlands.AlgebraicGeometry.PointTopology.GeometricRationalDensityExtension

/-! # The reductive coefficient spectral boundedness criterion over local fields -/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry
open Langlands.AlgebraicGeometry.PointTopology
open scoped CategoryTheory.MonObj Matrix

namespace Langlands.GroupScheme

/-- A closed faithful representation of a connected reductive group over a
nonarchimedean local field, all of whose rational-point matrices have integral
characteristic polynomials, has algebraically bounded rational points. -/
theorem reductiveSpectralBoundedness :
    ReductiveSpectralBoundednessStatement.{u} := by
  intro F _ _ _ _ G hG
  let : IsAffineHom G.X.hom := hG.isAffineHom
  let : IsAffine G.X.left := isAffine_of_isAffineHom G.X.hom
  intro N ρ hc hint
  have := hG.smooth
  have := hG.connectedSpace
  let α := baseChangeSectionHom (toAlgebraicClosure F) G
  have hα : ∀ g : rationalPoints G,
      α g = geometricRationalPoint (K := AlgebraicClosure F) G.X g := by
    intro g
    apply Over.OverMorphism.ext
    rw [baseChangeSectionHom_left]
    rfl
  apply isAlgebraicallyBounded_of_dense_geometricPointHom F G hG N ρ hc hint α hα
  have hd := hasDenseGeometricRationalPoints_of_hasDenseRationalPoints
    (K := AlgebraicClosure F) G.X (hasDenseRationalPoints_of_localField F G)
  change Dense (⋃ g : rationalPoints G, Set.range (α g).left)
  simp only [hα]
  change HasDenseGeometricRationalPoints F (AlgebraicClosure F) G.X
  exact hd

end Langlands.GroupScheme
