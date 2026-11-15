import Langlands.GroupScheme.AffineWeilRestrictionMaps
import Langlands.GroupScheme.AffineWeilRestrictionTopology
import Langlands.GroupScheme.Rational.Characters
import Langlands.AlgebraicGeometry.PointTopology.RationalPoints

/-! # Rational points of affine Weil restriction along a finite projective ring map -/

noncomputable section

universe u

set_option backward.isDefEq.respectTransparency false

open CategoryTheory Opposite AlgebraicGeometry
open scoped CategoryTheory.MonObj TensorProduct

namespace Langlands.GroupScheme.IntegralModel.EqualCharacteristicGreenberg

open Langlands.AlgebraicGeometry.PointTopology

section RingCoeff

variable (A : Type u) [CommRing A] (G : GroupScheme (Spec (CommRingCat.of A)))

/-- Over an arbitrary commutative base ring, identity-tested rational points are the
points with coefficients in the base algebra itself. -/
def ringCoeffEquiv : rationalPoints G ≃* G.affinePoints (CommAlgCat.of (CommRingCat.of A) A) :=
  (G.points.mapIso (ringTestSelfIso A).op).groupIsoToMulEquiv

@[simp] theorem ringCoeffEquiv_left (x : rationalPoints G) :
    (ringCoeffEquiv A G x).left = x.left := by
  change 𝟙 _ ≫ x.left = x.left
  simp

variable {A G} {H : GroupScheme (Spec (CommRingCat.of A))}

/-- The ring-coefficient comparison commutes with group-scheme homomorphisms. -/
theorem ringCoeffEquiv_map (f : G ⟶ H) (x : rationalPoints G) :
    ringCoeffEquiv A H (rationalPoints.map f x) =
      G.affinePointsTarget f (CommAlgCat.of (CommRingCat.of A) A) (ringCoeffEquiv A G x) := by
  rw [rationalPoints.map_apply, affinePointsTarget_apply]
  apply Over.OverMorphism.ext
  change 𝟙 _ ≫ (x ≫ f.hom.hom).left = (𝟙 _ ≫ x.left) ≫ f.hom.hom.left
  simp

end RingCoeff

section Weil

variable (A B : Type u) [CommRing A] [CommRing B] [Algebra A B]
  [Module.Finite A B] [Module.Projective A B]
  {G H : GroupScheme (Spec (CommRingCat.of B))}
  [IsAffine G.X.left] [LocallyOfFiniteType G.X.hom]
  [IsAffine H.X.left] [LocallyOfFiniteType H.X.hom]

/-- The base-point comparison of affine Weil restriction respects restricted homomorphisms
(ring-coefficient version of `AffineWeil.basePointsEquiv_map`). -/
theorem basePointsEquiv_map (f : G ⟶ H)
    (x : (AffineWeil.groupScheme A B G).affinePoints (CommAlgCat.of (CommRingCat.of A) A)) :
    AffineWeil.basePointsEquiv A B H
        ((AffineWeil.groupScheme A B G).affinePointsTarget (AffineWeil.map A B f)
          (CommAlgCat.of (CommRingCat.of A) A) x) =
      G.affinePointsTarget f (CommAlgCat.of (CommRingCat.of B) B)
        (AffineWeil.basePointsEquiv A B G x) := by
  change AffineWeil.tensorUnitPointsEquiv A B H
      (AffineWeil.pointsEquiv A B H A
        ((AffineWeil.groupScheme A B G).affinePointsTarget (AffineWeil.map A B f)
          (CommAlgCat.of (CommRingCat.of A) A) x)) = _
  rw [AffineWeil.map_affinePoints]
  exact DFunLike.congr_fun
    (G.affinePointsTarget_naturality f
      (CommAlgCat.ofHom (Algebra.TensorProduct.rid A B B).toAlgHom))
    (AffineWeil.pointsEquiv A B G A x)

/-- Rational points of the affine Weil restriction along a finite projective ring map are
the rational points of the original group scheme. -/
def weilRationalPointsEquiv (G : GroupScheme (Spec (CommRingCat.of B)))
    [IsAffine G.X.left] [LocallyOfFiniteType G.X.hom] :
    rationalPoints (AffineWeil.groupScheme A B G) ≃* rationalPoints G :=
  (ringCoeffEquiv A (AffineWeil.groupScheme A B G)).trans
    ((AffineWeil.basePointsEquiv A B G).trans (ringCoeffEquiv B G).symm)

/-- The rational-point comparison is natural for restricted homomorphisms. -/
theorem weilRationalPointsEquiv_map (f : G ⟶ H)
    (x : rationalPoints (AffineWeil.groupScheme A B G)) :
    weilRationalPointsEquiv A B H (rationalPoints.map (AffineWeil.map A B f) x) =
      rationalPoints.map f (weilRationalPointsEquiv A B G x) := by
  apply (ringCoeffEquiv B H).injective
  simp only [weilRationalPointsEquiv, MulEquiv.trans_apply, MulEquiv.apply_symm_apply]
  rw [ringCoeffEquiv_map, basePointsEquiv_map, ringCoeffEquiv_map, MulEquiv.apply_symm_apply]

end Weil

end Langlands.GroupScheme.IntegralModel.EqualCharacteristicGreenberg
