import Langlands.Geometry.Building.TorusValuationBuildingConstruction
import Langlands.GroupScheme.SimplyConnected.CommutativeDerivedCoverConstruction
import Langlands.Geometry.Building.KPZeroDatumConstruction
import Langlands.GroupScheme.Torus.BaseChange

/-! # Actual parahoric-building data of every local-field torus -/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry
open scoped CategoryTheory.MonObj
open Langlands.GroupScheme

namespace Langlands.Geometry.Building.ParahoricBuildingData

variable {F : Type u} [Field F] [ValuativeRel F] [TopologicalSpace F]
  [IsNonarchimedeanLocalField F]
  (T : CommGroupScheme (Spec (CommRingCat.of F)))

/-- Construct actual parahoric-building data for a torus, including the actual
simply connected derived covers and all unramified zero-subgroup choices. -/
def ofTorus (hT : IsTorus T.toGrp) :
    letI : IsAffineHom T.toGrp.X.hom := hT.isConnectedReductive_of_fieldSplitting.isAffineHom
    ParahoricBuildingData T.toGrp := by
  have hred := hT.isConnectedReductive_of_fieldSplitting
  have : IsAffineHom T.toGrp.X.hom := hred.isAffineHom
  let B := ValuationBuildingData.ofTorus T hT
  let c := commutativeDerivedCoverData T.toGrp hred
  let K := UnramifiedClosure F
  let ZK := GaloisPointComparison.baseChanged F K B.centralizer.Z
  have hZK : IsTorus ZK := by
    change IsTorus (GaloisPointComparison.baseChanged F K T.toGrp)
    exact hT.baseChange
  have : IsCommMonObj ZK.X := by
    change IsCommMonObj
      (((CommGroupScheme.baseChange (GaloisPointComparison.baseMap F K)).obj T).X)
    infer_instance
  let cZ := commutativeDerivedCoverData ZK hZK.isConnectedReductive_of_fieldSplitting
  exact ofDerivedCovers B c.val (𝟙 _) c.property cZ.val (𝟙 _) cZ.property

/-- Adding the actual zero data preserves the constructed valuation-building data. -/
@[simp]
theorem ofTorus_toValuationBuildingData (hT : IsTorus T.toGrp) :
    letI : IsAffineHom T.toGrp.X.hom := hT.isConnectedReductive_of_fieldSplitting.isAffineHom
    (ofTorus T hT).toValuationBuildingData = ValuationBuildingData.ofTorus T hT :=
  rfl

/-- The resulting torus data retain the full existing single-apartment axioms. -/
theorem ofTorus_satisfiesApartmentAxioms (hT : IsTorus T.toGrp) :
    letI : IsAffineHom T.toGrp.X.hom := hT.isConnectedReductive_of_fieldSplitting.isAffineHom
    (ofTorus T hT).SatisfiesApartmentAxioms :=
  ValuationBuildingData.ofTorus_satisfiesApartmentAxioms T hT

end Langlands.Geometry.Building.ParahoricBuildingData
