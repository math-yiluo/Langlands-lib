import Langlands.Geometry.Building.RootValuationBuildingConstructionStatement
import Langlands.Geometry.Building.ValuationApartmentAxiomsExistenceStatement
import Langlands.Geometry.Building.ActualApartmentSplittingStatement
import Langlands.Geometry.Building.AffineIwahoriTitsBuildingStatement
import Langlands.Geometry.Building.AffineIwahoriTitsStatement
import Langlands.Geometry.Building.TitsBuildingAxiomAssembly
import Langlands.Geometry.Building.BoundedOpenStabilizerConstruction
import Langlands.Geometry.Building.ApartmentFacetConstruction
import Langlands.Geometry.Building.RootReflectionProof
import Langlands.Geometry.Building.KPCentralizerZeroCompactOpenProof
import Langlands.Geometry.Building.ChamberIwahoriCompactOpenProof
import Langlands.Geometry.Building.KPZeroDatumConstruction
import Langlands.Geometry.Building.FacetFixingWeylReduction
import Langlands.GroupScheme.Rational.OpenRootGenerationProof
import Langlands.GroupScheme.Rational.MaximalSplitTorusConjugacyProof
import Langlands.GroupScheme.Rational.SimplyConnectedCentralizerProductProof
import Langlands.GroupScheme.SimplyConnected.DerivedCoverProof
import Langlands.GroupScheme.Reductive.AlgebraicExtensionAscent

/-! # The construction of the actual quotient and its five axioms, from four statements -/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry
open scoped CategoryTheory.MonObj
open Langlands.GroupScheme

namespace Langlands.Geometry.Building

namespace ParahoricBuildingData

variable {F : Type u} [Field F] [ValuativeRel F] [TopologicalSpace F]
  [IsNonarchimedeanLocalField F]
  {G : GroupScheme (Spec (CommRingCat.of F))} [IsAffineHom G.X.hom]

/-- Every actual valuation-building datum extends to parahoric-building data: the zero data
come from actual simply connected derived covers of `G` and of the centralizer over the
maximal unramified extension. The underlying valuation-building data are unchanged. -/
theorem exists_toValuationBuildingData_eq (B : ValuationBuildingData G) :
    ∃ P : ParahoricBuildingData G, P.toValuationBuildingData = B := by
  obtain ⟨D, C, d, π, hcover⟩ :=
    simplyConnectedDerivedCoverExistence F G B.isConnectedReductive
  have hZ : IsConnectedReductive
      (GaloisPointComparison.baseChanged F (UnramifiedClosure F) B.centralizer.Z) :=
    B.isConnectedReductive_centralizer.baseChange_of_algebraicExtension
  obtain ⟨DZ, CZ, dZ, πZ, hcoverZ⟩ :=
    simplyConnectedDerivedCoverExistence (UnramifiedClosure F) _ hZ
  exact ⟨ofDerivedCovers B d π hcover dZ πZ hcoverZ, rfl⟩

variable (P : ParahoricBuildingData G)

/-- The five axiom families on parahoric-building data satisfying the Chapter 7 apartment
axioms, from an actual apartment splitting, the affine Iwahori–Tits statement and its
identification with the building Tits system. -/
theorem fiveAxioms_of_statements (hD : P.SatisfiesApartmentAxioms)
    (hT : ∃ T : P.toValuationBuildingData.ApartmentSplitting,
      P.SatisfiesAffineApartmentAxiom T)
    (hIT : AffineIwahoriTitsStatement.{u}) (hIB : AffineIwahoriTitsBuildingStatement.{u}) :
    ∃ (R : P.toValuationBuildingData.PolysimplicialRealization)
      (T : P.toValuationBuildingData.ApartmentSplitting),
      P.SatisfiesBuildingAxiom R ∧
      P.HasBoundedOpenStabilizers ∧
      P.SatisfiesAffineApartmentAxiom T ∧
      P.HasRootReflections ∧
      P.SatisfiesApartmentAxioms ∧
      P.HasCompatibleApartmentFacets ∧
      P.HasTitsSystem := by
  obtain ⟨T, hTa⟩ := hT
  have hrank := P.hasRankOneFactorization_actual
  have hΨ := hD.isAffineRootSystem_affineRoots.isLocallyFiniteReflectionArrangement
  obtain ⟨x, hx⟩ := hΨ.exists_regularPoint
  have hCa :
      AffineRootSystem.IsChamber P.affineRoots (AffineRootSystem.facet P.affineRoots x) :=
    ⟨x, hx, rfl⟩
  obtain ⟨hN, hZ0, e, hW⟩ := hIT F G P hD _ hCa
  have hB := hIB F G P hD hN hZ0 _ e hCa hW
  refine ⟨hB.titsRealization, T, ?_, ?_, hTa, RootReflectionProof.hasRootReflections _, hD,
    P.toValuationBuildingData.hasCompatibleApartmentFacets_of_rankOne hD hrank, ?_⟩
  · exact P.satisfiesBuildingAxiom_affineTitsRealization_of_statements e
      hD.isAffineRootSystem_affineRoots hCa hB simplyConnectedCentralizerProduct
      maximalSplitTorusConjugacy
  · exact P.hasBoundedOpenStabilizers_of_rankOne_and_isOpen hD hrank
      RelativeRoot.openRootCentralizerGeneration P.centralizerZeroCompactOpen.2
  · intro Ca hCa'
    obtain ⟨hN', hZ0', e', hW'⟩ := hIT F G P hD Ca hCa'
    exact ⟨P.affinePart, inferInstance, P.affineTitsProjection,
      P.chamberSimpleInAffinePart e' Ca, hIB F G P hD hN' hZ0' Ca e' hCa' hW'⟩

end ParahoricBuildingData

/-- `RootValuationBuildingConstructionStatement` follows from the existence of actual
valuation-building data satisfying the Chapter 7 apartment axioms (KP Theorem 9.6.5), the
actual apartment splitting of KP Axiom 4.1.4, the `G(F)^0` affine Iwahori–Tits system of KP
Theorem 7.5.3 and its identification with the Tits system of KP Axiom 4.1.9 (KP
Propositions 7.6.3 and 7.6.4, Remark 7.6.5). -/
def RootValuationBuildingConstructionReductionStatement : Prop :=
  ValuationApartmentAxiomsExistenceStatement.{u} →
    ActualApartmentSplittingStatement.{u} →
      AffineIwahoriTitsStatement.{u} →
        AffineIwahoriTitsBuildingStatement.{u} →
          RootValuationBuildingConstructionStatement.{u}

/-- Proof of the reduction `RootValuationBuildingConstructionReductionStatement`. -/
theorem rootValuationBuildingConstructionReduction :
    RootValuationBuildingConstructionReductionStatement.{u} := by
  intro hA hS hIT hIB F _ _ _ _ G hG
  have : IsAffineHom G.X.hom := hG.isAffineHom
  obtain ⟨B, hD⟩ := hA F G hG
  obtain ⟨P, rfl⟩ := ParahoricBuildingData.exists_toValuationBuildingData_eq B
  obtain ⟨R, T, h⟩ :=
    P.fiveAxioms_of_statements hD (hS F G P.toValuationBuildingData hD) hIT hIB
  exact ⟨P, R, T, h⟩

end Langlands.Geometry.Building
