import Langlands.BruhatTits.IntegralModels.Transport.Family
import Langlands.Geometry.Building.FullValidity.DatumTransport.Building

/-! # KP model families on the based transport of building data

For `f : G ≅ H`, `σ : B.S ≅ S` and `j : S → H` with `B.i ≫ f = σ ≫ j`, the comparisons of
`B` with `B.basedTransport σ f h` form a `BuildingTransportPackage`. Hence the model family,
the facet quotients and KP Axioms 4.1.20 and 4.1.22 transfer to the parahoric data
`P.basedTransport σ f h`.
-/

set_option backward.isDefEq.respectTransparency false

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry
open scoped CategoryTheory.MonObj

namespace Langlands.BruhatTits.IntegralModels

open GroupScheme Geometry.Building

variable {K : Type u} [Field K] [ValuativeRel K] [TopologicalSpace K]
  [IsNonarchimedeanLocalField K]
  {G H : GroupScheme (Spec (CommRingCat.of K))} [IsAffineHom G.X.hom] [IsAffineHom H.X.hom]
  {S : CommGroupScheme (Spec (CommRingCat.of K))} {j : S.toGrp ⟶ H}

/-- The building transport package from `B` to `B.basedTransport σ f h`: the apartment map
`basedApartmentEquiv` and the building map `basedBuildingEquiv`. -/
def BuildingTransportPackage.based (B : ValuationBuildingData G) (σ : B.S ≅ S) (f : G ≅ H)
    (h : B.i ≫ f.hom = CommGroupScheme.groupHom σ.hom ≫ j) :
    BuildingTransportPackage B (B.basedTransport σ f h) f where
  σ := σ
  comm := h
  A := B.basedApartmentEquiv σ f h
  linear := rfl
  roots := B.transportedRoots_basedApartmentEquiv σ f h
  Φ := B.basedBuildingEquiv σ f h
  smul := B.basedBuildingEquiv_smul σ f h
  translated := B.basedBuildingEquiv_translatedApartmentMap σ f h

variable {R : Type u} [CommRing R] [IsDomain R] [Algebra R K] [IsFractionRing R K]
  [IsLocalRing R] (P : ParahoricBuildingData G) (σ : P.S ≅ S) (f : G ≅ H)
  (h : P.i ≫ f.hom = CommGroupScheme.groupHom σ.hom ≫ j)

/-- KP Axiom 4.1.20 for the model family transported to `P.basedTransport σ f h`. -/
theorem BuildingModelFamily.satisfiesModelAxioms_basedTransport
    {M : BuildingModelFamily P.toValuationBuildingData R} (hM : M.SatisfiesModelAxioms P) :
    (M.transport (BuildingTransportPackage.based P.toValuationBuildingData σ f h))
      |>.SatisfiesModelAxioms (P.basedTransport σ f h) :=
  BuildingModelFamily.satisfiesModelAxioms_transport _ hM rfl
    (P.basedTransport_zeroSubgroup σ f h)

/-- KP Axiom 4.1.22 for the facet quotients transported to `P.basedTransport σ f h`, with the
root datum transported along `σ` and `f`. -/
theorem BuildingModelQuotientFamily.satisfiesMorphismAxioms_basedTransport
    {M : BuildingModelFamily P.toValuationBuildingData R}
    {QF : BuildingModelQuotientFamily P.toValuationBuildingData M}
    {Droot : RelativeRootReflectionData P.i} (hQF : QF.SatisfiesMorphismAxioms Droot) :
    (QF.transport (BuildingTransportPackage.based P.toValuationBuildingData σ f h))
      |>.SatisfiesMorphismAxioms (Droot.transport σ f h) :=
  BuildingModelQuotientFamily.satisfiesMorphismAxioms_transport _ hQF

end Langlands.BruhatTits.IntegralModels
