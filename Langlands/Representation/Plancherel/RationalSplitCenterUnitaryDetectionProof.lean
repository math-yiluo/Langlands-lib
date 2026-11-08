import Langlands.Representation.Plancherel.RationalSplitCenterUnitaryDetectionStatement

/-! # Conditional split-center unitary-detection adapter -/

set_option autoImplicit false

noncomputable section

open CategoryTheory AlgebraicGeometry
open Langlands.AlgebraicGeometry.PointTopology
open Langlands.BruhatTits.RationalPoints
open scoped CategoryTheory.MonObj

namespace Langlands.Plancherel

universe u

/-- Instantiate generic unitary detection on the actual valuation projection. -/
theorem conditionalRationalSplitCenterUnitaryDetection :
    ConditionalRationalSplitCenterUnitaryDetectionStatement.{u} := by
  intro F _ _ _ _ M hM T s hs hinj hcompact hcocompact hderived
  let : IsAffineHom M.X.hom := hM.isAffineHom
  let : IsAffine M.X.left := isAffine_of_isAffineHom M.X.hom
  let : TopologicalSpace (GroupScheme.rationalPoints M) := rationalPointTopology F M.X
  let : Finite (rationalDiscreteValuationImage M ⧸
      (GroupScheme.rationalPoints.map s).range.map (rationalValuationImageProjection M)) :=
    finite_rationalValuationQuotient_of_injective hM s hs hinj
  apply Langlands.HarishChandraSchwartz.isUnitaryDetecting_of_norm_eq_one_on_ker
    (GroupScheme.rationalPoints.map s).range (rationalValuationImageProjection M)
  intro θ hθ g hg
  rw [rationalValuationImageProjection_ker] at hg
  exact norm_eq_one_on_rationalCommonNormKernel_of_structure M hM
    hcompact hcocompact hderived θ hθ g hg

end Langlands.Plancherel
