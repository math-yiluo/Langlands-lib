import Langlands.Global.IntegralClosureFractionTensor
import Langlands.AlgebraicGeometry.PointTopology.AffineChartWeilRestrictionSpecifiedTensorBaseChange

/-! # Original generic fiber of the integral-closure Weil model -/

noncomputable section

universe u

open CategoryTheory
open _root_.AlgebraicGeometry Langlands.Global

namespace Langlands.AlgebraicGeometry.PointTopology

set_option backward.isDefEq.respectTransparency false

variable (A B K L : Type u)
  [CommRing A] [IsDomain A] [CommRing B] [Field K] [Field L]
  [Algebra A K] [IsFractionRing A K] [Algebra K L] [FiniteDimensional K L]
  [Algebra A L] [IsScalarTower A K L]
  [Algebra A B] [Algebra B L] [IsScalarTower A B L] [IsIntegralClosure B A L]
  [Module.Finite A B] [Module.Projective A B]
  (Y : Over (Spec (CommRingCat.of B))) [LocallyOfFiniteType Y.hom]

local instance genericFiberLocallyOfFiniteType : LocallyOfFiniteType (ringBaseChange B L Y).hom :=
  inferInstanceAs (LocallyOfFiniteType
    (CategoryTheory.Limits.pullback.snd Y.hom (Spec.algebraMap B L)))

/-- The original generic fiber of the actual integral Weil model is the actual field Weil scheme. -/
def integralClosureWeilRestrictionGenericFiberIso [IsSeparated Y.hom]
    (hY : HasFiniteAffineNeighborhoods Y.left) :
    ringBaseChange A K (affineChartWeilRestriction A B Y) ≅
      affineChartWeilRestriction K L (ringBaseChange B L Y) :=
  affineChartWeilRestrictionSpecifiedTensorBaseChangeIso A B K L
    (integralClosureFractionTensorEquiv A B K L)
    (integralClosureFractionTensorEquiv_one_tmul A B K L) Y hY

/-- This scheme isomorphism retains the specified original-counit map on every actual test. -/
theorem integralClosureWeilRestrictionGenericFiberIso_comparison [IsSeparated Y.hom]
    (hY : HasFiniteAffineNeighborhoods Y.left)
    (T : Over (Spec (CommRingCat.of K)))
    (p : T ⟶ ringBaseChange A K (affineChartWeilRestriction A B Y)) :
    affineChartWeilRestrictionComparison K L (ringBaseChange B L Y) T
        (p ≫ (integralClosureWeilRestrictionGenericFiberIso A B K L Y hY).hom) =
      affineChartWeilRestrictionSpecifiedTensorComparison A B K L
        (integralClosureFractionTensorEquiv A B K L)
        (integralClosureFractionTensorEquiv_one_tmul A B K L) Y T p :=
  affineChartWeilRestrictionSpecifiedTensorBaseChangeIso_comparison A B K L
    (integralClosureFractionTensorEquiv A B K L)
    (integralClosureFractionTensorEquiv_one_tmul A B K L) Y hY T p

/-- A specified relative projective immersion derives all generic-fiber comparison geometry. -/
def projectiveImmersionIntegralClosureWeilRestrictionGenericFiberIso
    (n : ℕ) (j : Y.left ⟶ ProjectiveSpace B n) [IsImmersion j]
    (hj : j ≫ projectiveSpaceToSpec B n = Y.hom) :
    ringBaseChange A K (affineChartWeilRestriction A B Y) ≅
      affineChartWeilRestriction K L (ringBaseChange B L Y) := by
  let := isSeparated_of_projectiveImmersion B Y n j hj
  exact integralClosureWeilRestrictionGenericFiberIso A B K L Y
    (hasFiniteAffineNeighborhoods_of_projectiveImmersion B n j)

/-- The projective-immersion comparison retains the same original counit on all tests. -/
theorem projectiveImmersionIntegralClosureWeilRestrictionGenericFiberIso_comparison
    (n : ℕ) (j : Y.left ⟶ ProjectiveSpace B n) [IsImmersion j]
    (hj : j ≫ projectiveSpaceToSpec B n = Y.hom)
    (T : Over (Spec (CommRingCat.of K)))
    (p : T ⟶ ringBaseChange A K (affineChartWeilRestriction A B Y)) :
    affineChartWeilRestrictionComparison K L (ringBaseChange B L Y) T
        (p ≫ (projectiveImmersionIntegralClosureWeilRestrictionGenericFiberIso
          A B K L Y n j hj).hom) =
      affineChartWeilRestrictionSpecifiedTensorComparison A B K L
        (integralClosureFractionTensorEquiv A B K L)
        (integralClosureFractionTensorEquiv_one_tmul A B K L) Y T p := by
  let := isSeparated_of_projectiveImmersion B Y n j hj
  exact integralClosureWeilRestrictionGenericFiberIso_comparison A B K L Y
    (hasFiniteAffineNeighborhoods_of_projectiveImmersion B n j) T p

end Langlands.AlgebraicGeometry.PointTopology
