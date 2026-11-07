import Langlands.GroupScheme.GeometricComponentFieldBaseChange
import Langlands.GroupScheme.GeometricComponentRational

/-! # Rational classes and extension of the geometric base field -/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry
open scoped CategoryTheory.MonObj

namespace Langlands.GroupScheme.IdentityComponent

open GaloisPointComparison

section CoefficientTower

variable (k L M : Type u) [Field k] [Field L] [Field M]
  [Algebra k L] [Algebra k M] [Algebra L M] [IsScalarTower k L M]
  (H : GroupScheme (Spec (CommRingCat.of k)))

private theorem coefficient_section_extension
    (x : rationalPoints (baseChanged k L H)) :
    coefficientBaseChangeEquiv k L M H
        (baseChangeCoeffEquiv L M (baseChanged k L H)
          (baseChangeSectionHom (baseMap L M) (baseChanged k L H) x)) =
      GaloisPoint.relativeExtend k L M H (baseChangeCoeffEquiv k L H x) := by
  rw [← rationalExtend_eq_baseChangeSectionHom L M,
    baseChangeCoeffEquiv_rationalExtend, coefficientBaseChangeEquiv_extend,
    coefficientBaseChangeEquiv_rationalCoeffEquiv]

end CoefficientTower

section FieldExtension

variable (k K : Type u) [Field k] [Field K] [Algebra k K]
  [Algebra (AlgebraicClosure k) (AlgebraicClosure K)]
  [IsScalarTower k (AlgebraicClosure k) (AlgebraicClosure K)]
  (H : GroupScheme (Spec (CommRingCat.of k)))
  [Smooth H.X.hom] [IsAffineHom H.X.hom]

/-- On a base-field section the chosen closure comparison is the successive
actual pullback, first to K and then to its algebraic closure. -/
theorem geometricComponentBaseChangeSectionHom_rationalPoint (x : rationalPoints H) :
    geometricComponentBaseChangeSectionHom k K H
        (baseChangeSectionHom (baseMap k (AlgebraicClosure k)) H x) =
      baseChangeSectionHom (baseMap K (AlgebraicClosure K)) (baseChanged k K H)
        (baseChangeSectionHom (baseMap k K) H x) := by
  let : IsAffine H.X.left := isAffine_of_isAffineHom H.X.hom
  apply (baseChangeCoeffEquiv K (AlgebraicClosure K) (baseChanged k K H)).injective
  apply (coefficientBaseChangeEquiv k K (AlgebraicClosure K) H).injective
  rw [geometricComponentBaseChangeSectionHom_coefficient,
    coefficient_section_extension,
    ← rationalExtend_eq_baseChangeSectionHom k (AlgebraicClosure k),
    baseChangeCoeffEquiv_rationalExtend,
    ← rationalExtend_eq_baseChangeSectionHom k K,
    baseChangeCoeffEquiv_rationalExtend]
  exact (GaloisPoint.relativeExtend_extend k (AlgebraicClosure k) (AlgebraicClosure K)
    H _).trans (GaloisPoint.relativeExtend_extend k K (AlgebraicClosure K) H _).symm

/-- The chosen geometric comparison commutes with extension of rational
identity-component classes along the original field extension. -/
theorem geometricComponentBaseChangeEquiv_rational
    (c : RationalComponentQuotient H) :
    geometricComponentBaseChangeEquiv k K H (rationalGeometricComponentHom k H c) =
      rationalGeometricComponentHom K (baseChanged k K H)
        (rationalComponentBaseChange H (algebraMap k K) c) := by
  obtain ⟨x, rfl⟩ := rationalComponentProjection_surjective H c
  rw [rationalComponentBaseChange_projection, rationalGeometricComponentHom_projection,
    rationalGeometricComponentHom_projection, geometricComponentBaseChangeEquiv_ofPoint]
  exact congrArg (geometricComponentOfPoint K (baseChanged k K H))
    (geometricComponentBaseChangeSectionHom_rationalPoint k K H x)

/-- Original rational classes have a canonical image in the K-Galois-fixed
geometric components after extension to K. -/
def rationalGeometricComponentBaseChangeToFixed :
    RationalComponentQuotient H →*
      geometricComponentFixedSubgroup K (baseChanged k K H) :=
  (rationalGeometricComponentToFixed K (baseChanged k K H)).comp
    (rationalComponentBaseChange H (algebraMap k K))

@[simp]
theorem rationalGeometricComponentBaseChangeToFixed_val
    (c : RationalComponentQuotient H) :
    (rationalGeometricComponentBaseChangeToFixed k K H c).val =
      geometricComponentBaseChangeEquiv k K H (rationalGeometricComponentHom k H c) :=
  (geometricComponentBaseChangeEquiv_rational k K H c).symm

omit [Algebra (AlgebraicClosure k) (AlgebraicClosure K)]
  [IsScalarTower k (AlgebraicClosure k) (AlgebraicClosure K)] in
/-- Distinct original rational classes remain distinct in this fixed subgroup. -/
theorem rationalGeometricComponentBaseChangeToFixed_injective :
    Function.Injective (rationalGeometricComponentBaseChangeToFixed k K H) :=
  (rationalGeometricComponentToFixed_injective K (baseChanged k K H)).comp
    (rationalComponentBaseChange_injective H (algebraMap k K))

/-- Every transported original rational class is fixed by every K-Galois
coefficient automorphism, without a restriction map between Galois groups. -/
theorem geometricComponentBaseChangeEquiv_rational_smul
    (τ : Field.absoluteGaloisGroup K) (c : RationalComponentQuotient H) :
    τ • geometricComponentBaseChangeEquiv k K H (rationalGeometricComponentHom k H c) =
      geometricComponentBaseChangeEquiv k K H (rationalGeometricComponentHom k H c) := by
  rw [geometricComponentBaseChangeEquiv_rational]
  exact rationalGeometricComponentHom_smul K (baseChanged k K H) τ _

end FieldExtension

end Langlands.GroupScheme.IdentityComponent
