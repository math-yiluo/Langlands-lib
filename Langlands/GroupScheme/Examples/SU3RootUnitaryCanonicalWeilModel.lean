import Langlands.GroupScheme.IntegralModel.AffineWeilGeneric
import Langlands.GroupScheme.Examples.SU3RootUnitaryWeilIntegralModel

/-! # Canonical restrictions of actual unitary integral charts -/

noncomputable section

universe u

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 1000000
set_option synthInstance.maxHeartbeats 200000

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
  {I J : Type u} [Fintype I] [Fintype J]

local instance : IsAffine (unitaryParameterGroup K L).X.left := by
  change IsAffine (BilinearCoordinate.groupScheme (CommRingCat.of K)
    (canonicalCoordinateData.{u, u, u} K L).coeff).X.left
  let := BilinearCoordinate.isAffineHom (CommRingCat.of K)
    (canonicalCoordinateData.{u, u, u} K L).coeff
  exact isAffine_of_isAffineHom (BilinearCoordinate.groupScheme (CommRingCat.of K)
    (canonicalCoordinateData.{u, u, u} K L).coeff).X.hom

local instance : LocallyOfFiniteType (unitaryParameterGroup K L).X.hom := by
  change LocallyOfFiniteType (BilinearCoordinate.groupScheme (CommRingCat.of K)
    (canonicalCoordinateData.{u, u, u} K L).coeff).X.hom
  exact BilinearCoordinate.locallyOfFiniteType (CommRingCat.of K)
    (canonicalCoordinateData.{u, u, u} K L).coeff

local instance (C : IntegralChart O K L I) : IsAffine C.model.group.X.left :=
  isAffine_of_isAffineHom C.model.group.X.hom

local instance (C : IntegralChart O K L I) : Smooth C.model.group.X.hom :=
  C.model_isSmooth

/-- The actual generic unitary group restricted from K to F. -/
abbrev canonicalWeilGroup : GroupScheme (Spec (CommRingCat.of F)) :=
  AffineWeilGeneric.genericGroup A F O K (unitaryParameterGroup K L)

omit [Module.Projective A O] in
private theorem genericMap_id :
    AffineWeilGeneric.genericMap A F O K (𝟙 (unitaryParameterGroup K L)) =
      𝟙 (canonicalWeilGroup A F O K L) := by
  let := AffineWeilGeneric.genericFinite A F O K
  dsimp only [AffineWeilGeneric.genericMap]
  exact AffineWeil.map_id F K (G := unitaryParameterGroup K L)

variable (C : IntegralChart O K L I) (C' : IntegralChart O K L J)

/-- The actual restricted chart model with the canonical fraction-field identification. -/
def canonicalWeilModel : IntegralModel A F (canonicalWeilGroup A F O K L) :=
  AffineWeilGeneric.model A F O K C.model

theorem canonicalWeilModel_isSmooth :
    (C.canonicalWeilModel A F O K L).IsSmooth :=
  AffineWeilGeneric.model_isSmooth A F O K C.model

theorem canonicalWeilModel_hasGeometricallyConnectedFibres :
    (C.canonicalWeilModel A F O K L).HasGeometricallyConnectedFibres :=
  AffineWeilBilinear.restriction_geometricallyConnected A O C.coeff

variable (M : I → J → O) (t : O)
  (h : C.data.IsChartChange C'.data
    (fun i j => algebraMap O K (M i j)) (algebraMap O K t))

/-- Restriction of the actual chart transition extends the generic identity, using the
derived generic naturality square. -/
def canonicalWeilModelHom :
    (C.canonicalWeilModel A F O K L).Hom (C'.canonicalWeilModel A F O K L) (𝟙 _) := by
  simpa only [canonicalWeilModel, genericMap_id] using
    AffineWeilGeneric.modelHom A F O K C.model C'.model (C.chartHom C' M t h)

variable [IsLocalRing A]

include h in
/-- Every extension of the generic identity between the canonical restricted charts has
a smooth, connected, unipotent actual special-fibre kernel. -/
theorem canonicalWeilModel_kernel_properties
    (φ : (C.canonicalWeilModel A F O K L).Hom
      (C'.canonicalWeilModel A F O K L) (𝟙 _)) :
    Smooth (kernel φ.specialFibreMap).X.hom ∧
      ConnectedSpace (kernel φ.specialFibreMap).X.left ∧
        IsUnipotent (kernel φ.specialFibreMap) := by
  apply C.weilModel_kernel_properties A F C' M t h
    (AffineWeilGeneric.iso A F O K C.model)
    (AffineWeilGeneric.iso A F O K C'.model) _ φ
  simpa only [genericMap_id] using
    AffineWeilGeneric.iso_naturality A F O K C.model C'.model (C.chartHom C' M t h)

include h in
/-- Alternative presentations over A inherit the actual special-fibre kernel properties
under generic-compatible isomorphisms to the canonical restricted charts. -/
theorem canonicalWeilModel_presentation_kernel_properties
    {P Q : IntegralModel A F (canonicalWeilGroup A F O K L)}
    (e : P.Iso (C.canonicalWeilModel A F O K L) (CategoryTheory.Iso.refl _))
    (d : Q.Iso (C'.canonicalWeilModel A F O K L) (CategoryTheory.Iso.refl _))
    (φ : P.Hom Q (𝟙 _)) :
    Smooth (kernel φ.specialFibreMap).X.hom ∧
      ConnectedSpace (kernel φ.specialFibreMap).X.left ∧
        IsUnipotent (kernel φ.specialFibreMap) :=
  e.specialFibreKernel_properties d φ
    (C.canonicalWeilModelHom A F O K L C' M t h)
    (C.canonicalWeilModel_kernel_properties A F O K L C' M t h
      (C.canonicalWeilModelHom A F O K L C' M t h))

end SU3Root.IntegralChart

namespace SU3Root.IsRamifiedQuadraticValuation

open IntegralChart

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

/-- Actual restriction of the unitary lattice model X_{r,s} with its canonical generic
identification with restriction of U_{L/K}. -/
def canonicalWeilLatticeModel (r s : ℝ) :
    IntegralModel A F (canonicalWeilGroup A F O K L) :=
  (hω.latticeChart hO r s).canonicalWeilModel A F O K L

theorem canonicalWeilLatticeModel_isSmooth (r s : ℝ) :
    (hω.canonicalWeilLatticeModel A F O K L hO r s).IsSmooth :=
  (hω.latticeChart hO r s).canonicalWeilModel_isSmooth A F O K L

theorem canonicalWeilLatticeModel_hasGeometricallyConnectedFibres (r s : ℝ) :
    (hω.canonicalWeilLatticeModel A F O K L hO r s).HasGeometricallyConnectedFibres :=
  (hω.latticeChart hO r s).canonicalWeilModel_hasGeometricallyConnectedFibres A F O K L

/-- Ordered real lattice depths give an actual transition over the generic identity. -/
def canonicalWeilLatticeTransition {r₁ s₁ r₂ s₂ : ℝ}
    (hr : r₁ ≤ r₂) (hs : s₁ ≤ s₂) :
    (hω.canonicalWeilLatticeModel A F O K L hO r₂ s₂).Hom
      (hω.canonicalWeilLatticeModel A F O K L hO r₁ s₁) (𝟙 _) :=
  (hω.latticeChart hO r₂ s₂).canonicalWeilModelHom A F O K L
    (hω.latticeChart hO r₁ s₁) (hω.transitionMatrix hO r₁ r₂)
    (hω.transitionScalar hO r₁ s₁ r₂ s₂) (hω.isChartChange_transition hO hr hs)

variable [IsLocalRing A]

/-- At all coordinatewise ordered real lattice depths, including equal depths, every
generic-identity extension has a smooth, connected, unipotent special-fibre kernel. -/
theorem canonicalWeilLatticeModel_kernel_properties {r₁ s₁ r₂ s₂ : ℝ}
    (hr : r₁ ≤ r₂) (hs : s₁ ≤ s₂)
    (φ : (hω.canonicalWeilLatticeModel A F O K L hO r₂ s₂).Hom
      (hω.canonicalWeilLatticeModel A F O K L hO r₁ s₁) (𝟙 _)) :
    Smooth (kernel φ.specialFibreMap).X.hom ∧
      ConnectedSpace (kernel φ.specialFibreMap).X.left ∧
        IsUnipotent (kernel φ.specialFibreMap) :=
  (hω.latticeChart hO r₂ s₂).canonicalWeilModel_kernel_properties A F O K L
    (hω.latticeChart hO r₁ s₁) (hω.transitionMatrix hO r₁ r₂)
    (hω.transitionScalar hO r₁ s₁ r₂ s₂) (hω.isChartChange_transition hO hr hs) φ

/-- Generic-compatible presentations of the canonical restricted lattice models retain
the actual special-fibre kernel properties. -/
theorem canonicalWeilLatticeModel_presentation_kernel_properties {r₁ s₁ r₂ s₂ : ℝ}
    (hr : r₁ ≤ r₂) (hs : s₁ ≤ s₂)
    {P Q : IntegralModel A F (canonicalWeilGroup A F O K L)}
    (e : P.Iso (hω.canonicalWeilLatticeModel A F O K L hO r₂ s₂)
      (CategoryTheory.Iso.refl _))
    (d : Q.Iso (hω.canonicalWeilLatticeModel A F O K L hO r₁ s₁)
      (CategoryTheory.Iso.refl _))
    (φ : P.Hom Q (𝟙 _)) :
    Smooth (kernel φ.specialFibreMap).X.hom ∧
      ConnectedSpace (kernel φ.specialFibreMap).X.left ∧
        IsUnipotent (kernel φ.specialFibreMap) :=
  (hω.latticeChart hO r₂ s₂).canonicalWeilModel_presentation_kernel_properties A F O K L
    (hω.latticeChart hO r₁ s₁) (hω.transitionMatrix hO r₁ r₂)
    (hω.transitionScalar hO r₁ s₁ r₂ s₂) (hω.isChartChange_transition hO hr hs) e d φ

end SU3Root.IsRamifiedQuadraticValuation

end Langlands.GroupScheme
