import Langlands.AlgebraicGeometry.ProjectiveSpace.RationalCoordinates
import Langlands.AlgebraicGeometry.ProjectiveSpace.PointComparison
import Mathlib.RingTheory.Localization.Away.Basic

/-! # Evaluating projective affine-chart coordinates -/

noncomputable section

open CategoryTheory AlgebraicGeometry HomogeneousLocalization

attribute [local instance] MvPolynomial.gradedAlgebra

namespace Langlands.AlgebraicGeometry.ProjectiveSpace

universe u

variable {K : Type u} [Field K] (n : ℕ)

local instance (j : Fin (n + 1)) :
    Algebra K (Away (MvPolynomial.homogeneousSubmodule (Fin (n + 1)) K) (MvPolynomial.X j)) :=
  _root_.AlgebraicGeometry.ProjSpace.algebraAway K n j

/-- Evaluate a projective chart at a homogeneous vector with nonzero chart coordinate. -/
def coordinateChartMap (a : Fin (n + 1) → K) (j : Fin (n + 1)) (hj : a j ≠ 0) :
    Away (MvPolynomial.homogeneousSubmodule (Fin (n + 1)) K) (MvPolynomial.X j) →ₐ[K] K where
  toRingHom := (Localization.awayLift (MvPolynomial.eval a) (MvPolynomial.X j)
    (by simpa using (isUnit_iff_ne_zero.mpr hj))).comp
      (algebraMap (Away (MvPolynomial.homogeneousSubmodule (Fin (n + 1)) K)
        (MvPolynomial.X j)) (Localization.Away (MvPolynomial.X j)))
  commutes' r := by
    change Localization.awayLift (MvPolynomial.eval a) (MvPolynomial.X j)
      (by simpa using (isUnit_iff_ne_zero.mpr hj))
      (algebraMap K (Away (MvPolynomial.homogeneousSubmodule (Fin (n + 1)) K)
        (MvPolynomial.X j)) r).val = r
    rw [_root_.AlgebraicGeometry.ProjSpace.val_algebraMap,
      IsLocalization.Away.lift_eq]
    simp

@[simp]
theorem coordinateChartMap_ratio (a : Fin (n + 1) → K) (j : Fin (n + 1))
    (hj : a j ≠ 0) (k : Fin (n + 1)) :
    coordinateChartMap n a j hj (_root_.AlgebraicGeometry.ProjSpace.ratio K n j k) =
      a k / a j := by
  change Localization.awayLift (MvPolynomial.eval a) (MvPolynomial.X j)
    (by simpa using (isUnit_iff_ne_zero.mpr hj))
    (_root_.AlgebraicGeometry.ProjSpace.ratio K n j k).val = _
  rw [_root_.AlgebraicGeometry.ProjSpace.ratio, Away.val_mk]
  simpa [div_eq_mul_inv] using Localization.awayLift_mk (MvPolynomial.eval a)
    (MvPolynomial.X j) (MvPolynomial.X k) ((a j)⁻¹) (by simp [hj]) 1

/-- Re-evaluating the homogeneous coordinates in any nonvanishing chart gives the same point. -/
theorem chartPoint_coordinateChartMap (p : Spec (CommRingCat.of K) ⟶ ProjectiveSpace K n)
    (hp : p ≫ projectiveSpaceToSpec K n = 𝟙 _) (j : Fin (n + 1))
    (hj : pointCoordinates n p hp j ≠ 0) :
    chartPoint n j (coordinateChartMap n (pointCoordinates n p hp) j hj) = p := by
  let i := pointChartIndex n p hp
  have hi : IsUnit (pointCoordinates n p hp i) := by simp [i]
  have hpi (k : Fin (n + 1)) :
      pointChartMap n p hp (_root_.AlgebraicGeometry.ProjSpace.ratio K n i k) *
        pointCoordinates n p hp i = pointCoordinates n p hp k := by
    simp only [i, pointCoordinates_index, mul_one]
    rfl
  have hpj (k : Fin (n + 1)) :
      coordinateChartMap n (pointCoordinates n p hp) j hj
        (_root_.AlgebraicGeometry.ProjSpace.ratio K n j k) *
          pointCoordinates n p hp j = pointCoordinates n p hp k := by
    rw [coordinateChartMap_ratio, div_mul_cancel₀ _ hj]
  have he := _root_.AlgebraicGeometry.ProjSpace.specMap_comp_awayInclusion_eq_of_forall_apply_ratio_mul_eq
    K n K (pointCoordinates n p hp) i j hi (isUnit_iff_ne_zero.mpr hj)
    (pointChartMap n p hp) (coordinateChartMap n (pointCoordinates n p hp) j hj) hpi hpj
  change chartPoint n i (pointChartMap n p hp) =
    chartPoint n j (coordinateChartMap n (pointCoordinates n p hp) j hj) at he
  rw [← he]
  exact chartPoint_pointChartMap n p hp

end Langlands.AlgebraicGeometry.ProjectiveSpace
