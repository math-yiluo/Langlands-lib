import Langlands.GroupScheme.Examples.SU3RootUnitaryCanonicalWeilModel
import Langlands.GroupScheme.IntegralModel.AffineWeilPoints

/-! # Actual integral points of canonical restricted unitary models -/

noncomputable section

universe u

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 1000000
set_option synthInstance.maxHeartbeats 200000
set_option maxRecDepth 3000

open CategoryTheory AlgebraicGeometry
open scoped CategoryTheory.MonObj

namespace Langlands.GroupScheme

namespace SU3Root.IntegralChart

open IntegralModel

variable (A F O K L : Type u)
  [CommRing A] [IsDomain A] [Field F] [Algebra A F] [IsFractionRing A F]
  [CommRing O] [IsDomain O] [Field K] [Algebra O K] [IsFractionRing O K]
  [Algebra A O] [Algebra A K] [Algebra F K]
  [IsScalarTower A O K] [IsScalarTower A F K]
  [Module.Finite A O] [Module.Projective A O]
  [Field L] [Algebra K L] [Algebra.IsQuadraticExtension K L] [Algebra.IsSeparable K L]
  {I : Type u} [Fintype I]

local instance canonicalWeilPoints_unitaryAffine :
    IsAffine (unitaryParameterGroup K L).X.left := by
  change IsAffine (BilinearCoordinate.groupScheme (CommRingCat.of K)
    (canonicalCoordinateData.{u, u, u} K L).coeff).X.left
  let := BilinearCoordinate.isAffineHom (CommRingCat.of K)
    (canonicalCoordinateData.{u, u, u} K L).coeff
  exact isAffine_of_isAffineHom (BilinearCoordinate.groupScheme (CommRingCat.of K)
    (canonicalCoordinateData.{u, u, u} K L).coeff).X.hom

local instance canonicalWeilPoints_unitaryFinite :
    LocallyOfFiniteType (unitaryParameterGroup K L).X.hom := by
  change LocallyOfFiniteType (BilinearCoordinate.groupScheme (CommRingCat.of K)
    (canonicalCoordinateData.{u, u, u} K L).coeff).X.hom
  exact BilinearCoordinate.locallyOfFiniteType (CommRingCat.of K)
    (canonicalCoordinateData.{u, u, u} K L).coeff

local instance canonicalWeilPoints_modelSmooth (C : IntegralChart O K L I) :
    Smooth C.model.group.X.hom := C.model_isSmooth

/-- Rational points of the actual generic restriction are the original unitary parameters. -/
def canonicalWeilRationalPointsEquiv :
    rationalPoints (canonicalWeilGroup A F O K L) ≃* rationalParameters K L :=
  (AffineWeilGeneric.genericSectionsEquiv A F O K (G := unitaryParameterGroup K L)).trans
    (unitaryRationalPointsEquiv K L)

variable (C : IntegralChart O K L I)

/-- Integral sections of the actual restricted chart have its original integral coordinates. -/
def canonicalWeilIntegralCoordinatesEquiv :
    (C.canonicalWeilModel A F O K L).integralSections ≃*
      BilinearCoordinate.Coordinates C.coeff :=
  (AffineWeilGeneric.modelSectionsEquiv A F O K C.model).trans C.integralCoordinatesEquiv

theorem canonicalWeilRationalPointsEquiv_integralPointMap
    (x : (C.canonicalWeilModel A F O K L).integralSections) :
    canonicalWeilRationalPointsEquiv A F O K L
        ((C.canonicalWeilModel A F O K L).integralPointMap x) =
      fieldPoint C.data
        (fun i => algebraMap O K ((C.canonicalWeilIntegralCoordinatesEquiv A F O K L x).vec i))
        (algebraMap O K (C.canonicalWeilIntegralCoordinatesEquiv A F O K L x).scalar) := by
  change unitaryRationalPointsEquiv K L
    (AffineWeilGeneric.genericSectionsEquiv A F O K
      ((AffineWeilGeneric.model A F O K C.model).integralPointMap x)) = _
  rw [AffineWeilGeneric.model_integralPointMap]
  exact C.unitaryRationalPointsEquiv_integralPointMap _

theorem mem_integralPoints_canonicalWeilModel_iff
    (g : rationalPoints (canonicalWeilGroup A F O K L)) :
    g ∈ (C.canonicalWeilModel A F O K L).integralPoints ↔
      ∃ (a : I → O) (b : O), canonicalWeilRationalPointsEquiv A F O K L g =
        fieldPoint C.data (fun i => algebraMap O K (a i)) (algebraMap O K b) := by
  change g ∈ (AffineWeilGeneric.model A F O K C.model).integralPoints ↔ _
  rw [AffineWeilGeneric.model_mem_integralPoints, C.mem_integralPoints_iff]
  rfl

end SU3Root.IntegralChart

namespace SU3Root.IsRamifiedQuadraticValuation

open IntegralChart

attribute [local instance] canonicalWeilPoints_unitaryAffine canonicalWeilPoints_unitaryFinite
  canonicalWeilPoints_modelSmooth

variable (A F O K L : Type u)
  [CommRing A] [IsDomain A] [Field F] [Algebra A F] [IsFractionRing A F]
  [CommRing O] [IsDomain O] [Field K] [Algebra O K] [IsFractionRing O K]
  [Algebra A O] [Algebra A K] [Algebra F K]
  [IsScalarTower A O K] [IsScalarTower A F K]
  [Module.Finite A O] [Module.Projective A O]
  [Field L] [Algebra K L] [Algebra.IsQuadraticExtension K L] [Algebra.IsSeparable K L]
  {ω : AddValuation L (WithTop ℝ)}
  (hω : IsRamifiedQuadraticValuation K L ω)
  (hO : IsValuationIntegers O K ω)

/-- Integral points of the actual canonical restriction are exactly the original
unitary filtration product, for arbitrary real depths. -/
theorem mem_integralPoints_canonicalWeilLatticeModel_iff (r s : ℝ)
    (g : rationalPoints (canonicalWeilGroup A F O K L)) :
    g ∈ (hω.canonicalWeilLatticeModel A F O K L hO r s).integralPoints ↔
      canonicalWeilRationalPointsEquiv A F O K L g ∈ hω.filtrationProduct r s := by
  letI : Smooth (hω.latticeModel hO r s).group.X.hom :=
    hω.latticeModel_isSmooth hO r s
  change g ∈ (IntegralModel.AffineWeilGeneric.model A F O K
    (hω.latticeModel hO r s)).integralPoints ↔ _
  rw [IntegralModel.AffineWeilGeneric.model_mem_integralPoints,
    hω.mem_integralPoints_latticeModel_iff]
  rfl

theorem integralPoints_canonicalWeilLatticeModel_map (r s : ℝ) :
    (hω.canonicalWeilLatticeModel A F O K L hO r s).integralPoints.map
        (canonicalWeilRationalPointsEquiv A F O K L).toMonoidHom =
      hω.filtrationProduct r s := by
  ext p
  rw [Subgroup.mem_map]
  constructor
  · rintro ⟨g, hg, rfl⟩
    exact (hω.mem_integralPoints_canonicalWeilLatticeModel_iff A F O K L hO r s g).mp hg
  · intro hp
    refine ⟨(canonicalWeilRationalPointsEquiv A F O K L).symm p, ?_,
      MulEquiv.apply_symm_apply _ p⟩
    apply (hω.mem_integralPoints_canonicalWeilLatticeModel_iff A F O K L hO r s _).mpr
    rw [MulEquiv.apply_symm_apply]
    exact hp

theorem integralPoints_canonicalWeilLatticeModel_comap (r s : ℝ) :
    (hω.canonicalWeilLatticeModel A F O K L hO r s).integralPoints =
      (hω.filtrationProduct r s).comap
        (canonicalWeilRationalPointsEquiv A F O K L).toMonoidHom := by
  ext g
  exact hω.mem_integralPoints_canonicalWeilLatticeModel_iff A F O K L hO r s g

end SU3Root.IsRamifiedQuadraticValuation

end Langlands.GroupScheme
