import Langlands.GroupScheme.IntegralModel
import Langlands.AlgebraicGeometry.PointTopology.GeometricRationalDensityExtension

/-! # Scalar extension of actual rational points as a group homomorphism -/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry
open Langlands.AlgebraicGeometry.PointTopology
open scoped CategoryTheory.MonObj

namespace Langlands.GroupScheme

variable {F K : Type u} [Field F] [Field K] [Algebra F K]
  (G : GroupScheme (Spec (CommRingCat.of F)))

/-- The canonical homomorphism extending actual rational points to a field extension. -/
def geometricRationalPointHom :
    rationalPoints G →*
      rationalPoints
        ((GroupScheme.baseChange
          (Spec.map (CommRingCat.ofHom (algebraMap F K)))).obj G) :=
  baseChangeSectionHom (Spec.map (CommRingCat.ofHom (algebraMap F K))) G

/-- The canonical point homomorphism is the actual pullback section. -/
@[simp]
theorem geometricRationalPointHom_apply (g : rationalPoints G) :
    geometricRationalPointHom (K := K) G g =
      geometricRationalPoint (K := K) G.X g := by
  apply Over.OverMorphism.ext
  change (baseChangeSectionHom
    (Spec.map (CommRingCat.ofHom (algebraMap F K))) G g).left = _
  rw [baseChangeSectionHom_left]
  rfl

/-- As a function, scalar extension agrees with the existing geometric-point map. -/
theorem geometricRationalPointHom_eq :
    (geometricRationalPointHom (K := K) G : _ → _) =
      geometricRationalPoint (K := K) G.X := by
  funext g
  exact geometricRationalPointHom_apply G g

/-- The range is precisely the image used for coefficient transport. -/
theorem range_geometricRationalPointHom :
    Set.range (geometricRationalPointHom (K := K) G) =
      geometricRationalPoint (K := K) G.X ''
        (Set.univ : Set (RationalPoint F G.X)) := by
  erw [geometricRationalPointHom_eq, Set.image_univ]
  rfl

/-- Density of ground-field rational points gives density of their actual
scalar-extended sections, indexed by the canonical point homomorphism. -/
theorem dense_geometricRationalPointHom
    (hG : HasDenseRationalPoints F G.X) :
    Dense (⋃ g : rationalPoints G,
      Set.range (geometricRationalPointHom (K := K) G g).left) := by
  have h := hasDenseGeometricRationalPoints_of_hasDenseRationalPoints (K := K) G.X hG
  change Dense (⋃ g : RationalPoint F G.X,
    Set.range (geometricRationalPoint (K := K) G.X g).left) at h
  convert! h using 1
  simp only [geometricRationalPointHom_apply]
  rfl

end Langlands.GroupScheme
