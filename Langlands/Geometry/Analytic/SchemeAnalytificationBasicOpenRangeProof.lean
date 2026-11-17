import Langlands.Geometry.Analytic.SchemeAnalytificationCenterRangeProof
import Langlands.Geometry.Analytic.AffineAnalytificationImmersionProof

/-! # Principal-open ranges for scheme analytification -/

noncomputable section

universe u

namespace Langlands.Analytic.SchemeAnalytification.OpenGluing

open CategoryTheory _root_.AlgebraicGeometry Topology
open Langlands.Analytic.AffineSchemeAnalytification

variable (K : Type u) [NontriviallyNormedField K] [IsUltrametricDist K] [CompleteSpace K]

/-- The localization range formula applies to the algebra structure induced by
any specified algebra map. -/
theorem range_baseMap_of_localization
    {A B : Type u} [CommRing A] [CommRing B] [Algebra K A] [Algebra K B]
    (P : FinitePolynomialPresentation K A) (Q : FinitePolynomialPresentation K B)
    (g : A →ₐ[K] B) (a : A)
    (h : letI := g.toRingHom.toAlgebra; IsLocalization.Away a B) :
    Set.range (AffineAnalytification.baseMap K P Q g) =
      {z | AffineAnalytification.pointSeminorm K P z a ≠ 0} := by
  let : Algebra A B := g.toRingHom.toAlgebra
  let : IsScalarTower K A B := IsScalarTower.of_algHom g
  let : IsLocalization.Away a B := h
  have heq : IsScalarTower.toAlgHom K A B = g := by
    ext b
    rfl
  rw [← heq]
  exact AffineAnalytification.ImmersionComparison.range_baseMap_away K P Q a

variable {X : Scheme.{u}} (f : X ⟶ Spec (CommRingCat.of K)) [LocallyOfFiniteType f]

/-- Restriction from a principal affine open has the expected local-center range. -/
theorem range_localMap_basicOpen (U : X.affineOpens) (a : Γ(X, U.val)) :
    Set.range (localMap K f (X.affineBasicOpen_le a)) =
      localCenter K f U ⁻¹' (X.basicOpen a : Set X) := by
  apply CenterRange.range_localMap_basicOpen_of_nonvanishing K f U a
  exact range_baseMap_of_localization K
    (chartPresentation K f U) (chartPresentation K f (X.affineBasicOpen a))
    (restriction f (X.affineBasicOpen_le a)) (CenterRange.basicOpenGenerator f U a)
    (CenterRange.isLocalization_restriction_basicOpen f U a)

/-- Principal affine restrictions satisfy the range input to the center reductions. -/
theorem basicOpenRangeData : CenterRange.BasicOpenRangeData K f :=
  range_localMap_basicOpen K f

/-- The global chart range is the inverse image of its affine open under the center. -/
theorem range_ι (U : X.affineOpens) :
    center K f ⁻¹' ((U : X.Opens) : Set X) = Set.range (ι K f U) :=
  CenterRange.range_ι K f (basicOpenRangeData K f) U

end Langlands.Analytic.SchemeAnalytification.OpenGluing
