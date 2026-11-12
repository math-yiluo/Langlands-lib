import Langlands.Geometry.Building.FullValidity.DatumTransportStatement
import Langlands.Geometry.Building.FullValidity.DatumTransport.Tits
import Langlands.Geometry.Building.FullValidity.DatumTransport.Bounded
import Langlands.Geometry.Building.FullValidity.DatumTransport.Iwahori
import Langlands.BruhatTits.IntegralModels.Transport.Based

/-!
# Proof of `KPBuildingDatumTransportStatement`

For a full corrected KP datum `D` on `G`, an isomorphism `f : G ≅ H` and a torus isomorphism
`σ : S_D ≅ S` with `i_D ≫ f = σ ≫ j`, `D.basedTransport σ f h` is the full datum on `H` whose
components are the based transports of the components of `D`. It satisfies all group axioms
when `D` does, and the building comparison `basedBuildingEquiv` is equivariant along
`rationalPoints.map f.hom` with inverse an isomorphism of buildings.
-/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry
open scoped CategoryTheory.MonObj
open Langlands.GroupScheme Langlands.BruhatTits.IntegralModels

namespace Langlands.Geometry.Building

namespace KPBuildingDatum

variable {F : Type u} [Field F] [ValuativeRel F] [TopologicalSpace F]
  [IsNonarchimedeanLocalField F]
  {G H : GroupScheme (Spec (CommRingCat.of F))} [IsAffineHom G.X.hom] [IsAffineHom H.X.hom]
  (D : KPBuildingDatum G) {S : CommGroupScheme (Spec (CommRingCat.of F))}
  {j : S.toGrp ⟶ H} (σ : D.base.S ≅ S) (f : G ≅ H)
  (h : D.base.i ≫ f.hom = CommGroupScheme.groupHom σ.hom ≫ j)

/-- The full KP datum on `H` transported from `D` along `σ` and `f`: the based transports of
the parahoric building data, the realization, the apartment splitting, the model family, the
quotient family (both along the package `BuildingTransportPackage.based`) and the root
reflection data. -/
def basedTransport : KPBuildingDatum H :=
  haveI := mono_of_isMaximalSplitTorus (D.base.isMaximalSplitTorus_of_basedIso σ f h)
  { base := D.base.basedTransport σ f h
    realization := D.realization.basedTransport D.base.toValuationBuildingData σ f h
    splitting := D.splitting.basedTransport D.base.toValuationBuildingData σ f h
    models := D.models.transport
      (BuildingTransportPackage.based D.base.toValuationBuildingData σ f h)
    quotients := D.quotients.transport
      (BuildingTransportPackage.based D.base.toValuationBuildingData σ f h)
    rootDatum := D.rootDatum.transport σ f h }

@[simp] theorem basedTransport_base :
    (D.basedTransport σ f h).base = D.base.basedTransport σ f h :=
  rfl

variable {D}

/-- All group axioms of `D` give the group axioms of `D.basedTransport σ f h`. -/
theorem SatisfiesGroupAxioms.basedTransport (hD : D.SatisfiesGroupAxioms) :
    (D.basedTransport σ f h).SatisfiesGroupAxioms where
  building := ValuationBuildingData.SatisfiesBuildingAxiom.basedTransport
    D.base.toValuationBuildingData σ f h hD.building
  boundedSubgroups := ValuationBuildingData.HasBoundedOpenStabilizers.basedTransport
    D.base.toValuationBuildingData σ f h hD.boundedSubgroups
  affineStructure := ValuationBuildingData.SatisfiesAffineApartmentAxiom.basedTransport
    D.base.toValuationBuildingData σ f h hD.affineStructure
  affineRootSystem :=
    { rootReflections := ValuationBuildingData.HasRootReflections.basedTransport
        D.base.toValuationBuildingData σ f h hD.affineRootSystem.rootReflections
      apartmentAxioms := ValuationBuildingData.SatisfiesApartmentAxioms.basedTransport
        D.base.toValuationBuildingData σ f h hD.affineRootSystem.apartmentAxioms
      compatibleApartmentFacets :=
        ValuationBuildingData.HasCompatibleApartmentFacets.basedTransport
          D.base.toValuationBuildingData σ f h hD.affineRootSystem.compatibleApartmentFacets }
  rootGroupAction := (satisfiesRootGroupActionAxiom_iff _).2
    ⟨ParahoricBuildingData.HasZeroFixerGenerators.basedTransport D.base σ f h
        hD.rootGroupAction.zeroFixerGenerators,
      ParahoricBuildingData.HasRootZeroFixers.basedTransport D.base σ f h
        hD.rootGroupAction.rootZeroFixers⟩
  titsSystem := ParahoricBuildingData.HasTitsSystem.basedTransport D.base σ f h hD.titsSystem
  iwahoriDecomposition := hD.iwahoriDecomposition.basedTransport σ f h
  bruhatTitsGroupSchemes := BuildingModelFamily.satisfiesModelAxioms_basedTransport
    D.base σ f h hD.bruhatTitsGroupSchemes
  reductiveQuotients := BuildingModelQuotientFamily.satisfiesMorphismAxioms_basedTransport
    D.base σ f h hD.reductiveQuotients

end KPBuildingDatum

/-- Proof of `KPBuildingDatumTransportStatement`: the transported datum
`D.basedTransport σ f h` has torus `S` and inclusion `i` by definition, satisfies the group
axioms by `SatisfiesGroupAxioms.basedTransport`, and its reduced building is compared with that
of `D` by `basedBuildingEquiv`, an equivariant isomorphism of buildings along
`rationalPoints.map f.hom` whose inverse is an isomorphism of buildings. -/
theorem kpBuildingDatumTransportStatement : KPBuildingDatumTransportStatement.{u} := by
  intro F _ _ _ _ G H _ _ D hD S i f σ h
  exact ⟨D.basedTransport σ f h, hD.basedTransport σ f h, rfl, HEq.rfl,
    D.base.basedBuildingEquiv σ f h,
    D.base.toValuationBuildingData.isEquivariantBuildingIso_basedBuildingEquiv σ f h,
    D.base.toValuationBuildingData.isBuildingIso_basedBuildingEquiv_symm σ f h⟩

end Langlands.Geometry.Building
