import Langlands.GroupScheme.AffineWeilRestrictionMaps
import Langlands.GroupScheme.AffineWeilRestrictionTopology
import Langlands.GroupScheme.GaloisPointRational

/-! # Actual rational-point comparison for affine Weil restriction -/

noncomputable section

universe u

open CategoryTheory Opposite AlgebraicGeometry
open scoped CategoryTheory.MonObj TensorProduct

namespace Langlands.GroupScheme.AffineWeil

variable (F E : Type u) [Field F] [Field E] [Algebra F E] [FiniteDimensional F E]
  {G H : GroupScheme (Spec (CommRingCat.of E))}
  [IsAffine G.X.left] [LocallyOfFiniteType G.X.hom]
  [IsAffine H.X.left] [LocallyOfFiniteType H.X.hom]

/-- The canonical base-point comparison respects actual restricted homomorphisms. -/
theorem basePointsEquiv_map (f : G ⟶ H)
    (x : (groupScheme F E G).affinePoints (CommAlgCat.of (CommRingCat.of F) F)) :
    basePointsEquiv F E H
        ((groupScheme F E G).affinePointsTarget (map F E f)
          (CommAlgCat.of (CommRingCat.of F) F) x) =
      G.affinePointsTarget f (CommAlgCat.of (CommRingCat.of E) E)
        (basePointsEquiv F E G x) := by
  change tensorUnitPointsEquiv F E H
      (pointsEquiv F E H F
        ((groupScheme F E G).affinePointsTarget (map F E f)
          (CommAlgCat.of (CommRingCat.of F) F) x)) = _
  rw [map_affinePoints]
  exact DFunLike.congr_fun
    (G.affinePointsTarget_naturality f
      (CommAlgCat.ofHom (Algebra.TensorProduct.rid F E E).toAlgHom))
    (pointsEquiv F E G F x)

/-- Rational points of the actual affine Weil restriction are the original E-rational points. -/
def rationalPointsEquiv (G : GroupScheme (Spec (CommRingCat.of E)))
    [IsAffine G.X.left] [LocallyOfFiniteType G.X.hom] :
    rationalPoints (groupScheme F E G) ≃* rationalPoints G :=
  (GaloisPointComparison.rationalCoeffEquiv F (groupScheme F E G)).trans
    ((basePointsEquiv F E G).trans (GaloisPointComparison.rationalCoeffEquiv E G).symm)

/-- The rational-point comparison is natural for the actual restricted homomorphism. -/
theorem rationalPointsEquiv_map (f : G ⟶ H)
    (x : rationalPoints (groupScheme F E G)) :
    rationalPointsEquiv F E H (rationalPoints.map (map F E f) x) =
      rationalPoints.map f (rationalPointsEquiv F E G x) := by
  apply (GaloisPointComparison.rationalCoeffEquiv E H).injective
  simp only [rationalPointsEquiv, MulEquiv.trans_apply, MulEquiv.apply_symm_apply]
  rw [GaloisPointComparison.rationalCoeffEquiv_map, basePointsEquiv_map,
    GaloisPointComparison.rationalCoeffEquiv_map, MulEquiv.apply_symm_apply]

end Langlands.GroupScheme.AffineWeil
