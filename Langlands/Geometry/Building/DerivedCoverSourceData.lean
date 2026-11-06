import Langlands.Geometry.Building.DerivedCoverBuildingComparison
import Langlands.Geometry.Building.CentralizerDatumConstruction
import Langlands.GroupScheme.SimplyConnected.DerivedCoverSplitTorusStatement
import Langlands.GroupScheme.Derived.CentralSplitTorusProductStatement
import Langlands.GroupScheme.Rational.SplitComponentProof
import Langlands.GroupScheme.Rational.SplitCentralEmbedding

/-! # Assembling the actual derived-cover source from universal structural inputs -/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry
open scoped CategoryTheory.MonObj
open Langlands.GroupScheme Langlands.BruhatTits

namespace Langlands.Geometry.Building.ParahoricBuildingData

variable {F : Type u} [Field F] [ValuativeRel F] [TopologicalSpace F]
    [IsNonarchimedeanLocalField F]
    {G : GroupScheme (Spec (CommRingCat.of F))} [IsAffineHom G.X.hom]
    (P : ParahoricBuildingData G)

local instance : IsAffineHom P.zeroDatum.C.X.hom :=
  P.zeroDatum.isSimplyConnectedDerivedCover.isSimplyConnectedCover.isSimplyConnected.isSemisimple.isConnectedReductive.isAffineHom

/-- Source building data on the actual cover stored in `P`, with original
root and action comparisons and lifts of the required normalizer intersection. -/
structure DerivedCoverSourceData where
  building : ValuationBuildingData P.zeroDatum.C
  normalizerHom : normalizerPoints building.i →* normalizerPoints P.i
  apartmentEquiv : building.Apartment ≃ᵃ[ℝ] P.Apartment
  transportedRoots_eq :
    AffineRootSystem.transportedRoots apartmentEquiv building.affineRoots = P.affineRoots
  equivariant : ∀ (n : normalizerPoints building.i) (x : building.Apartment),
    apartmentEquiv (n • x) = normalizerHom n • apartmentEquiv x
  lifts : ∀ n : normalizerPoints P.i,
    n ∈ P.simplyConnectedImage.subgroupOf (normalizerPoints P.i) →
      ∃ m : normalizerPoints building.i, normalizerHom m = n
  normalizerHom_coe : ∀ n : normalizerPoints building.i,
    (normalizerHom n : rationalPoints G) =
      rationalPoints.map (P.zeroDatum.π ≫ P.zeroDatum.d) n.val

/-- Choose the actual covering tori and central component and construct all
source building and comparison data from the three exact universal inputs. -/
def derivedCoverSourceData
    (htori : SimplyConnectedDerivedCoverSplitTorusStatement.{u})
    (hproduct : DerivedCentralSplitTorusProductStatement.{u})
    (hcomparison : Cartan.CentralizerValuationComparisonStatement.{u}) :
    P.DerivedCoverSourceData :=
  Classical.choice <| by
    have : Smooth G.X.hom := P.isConnectedReductive.smooth
    obtain ⟨T, j, e, hj, he, h, U, k, f, hk, h', hf, -⟩ :=
      htori F G P.zeroDatum.D P.zeroDatum.C P.zeroDatum.d P.zeroDatum.π
        P.zeroDatum.isSimplyConnectedDerivedCover P.S P.i P.isMaximalSplitTorus
    obtain ⟨A, a, ha⟩ := (splitComponentStatement F G P.isConnectedReductive).1
    obtain ⟨c, hca, -, -⟩ :=
      ha.exists_commFactor_of_isMaximalSplitTorus P.isMaximalSplitTorus
    have hp : IsCentralIsogeny (RelativeRoot.centralComplementProduct e c) :=
      hproduct F G P.zeroDatum.D P.zeroDatum.d P.isConnectedReductive
        P.zeroDatum.isSimplyConnectedDerivedCover.isDerivedSubgroup
        P.S T A P.i j e a c P.isMaximalSplitTorus hj he h ha hca
    have : Flat (RelativeRoot.centralComplementProduct e c).hom.hom.left := hp.flat
    have : Surjective (RelativeRoot.centralComplementProduct e c).hom.hom.left := hp.surjective
    have : Mono j.hom.hom.left := mono_of_isMaximalSplitTorus hj
    have : Mono k.hom.hom.left := mono_of_isMaximalSplitTorus hk
    have hA : IsSplitTorus A.toGrp := ha.isCentralSplitTorus.1.1
    have hc : IsCentral (CommGroupScheme.groupHom c ≫ P.i) := by
      rw [hca]
      exact ha.isCentralSplitTorus.2
    let CD := CentralizerDatum.ofValuationComparison hcomparison
      P.zeroDatum.isSimplyConnectedDerivedCover.isSimplyConnectedCover.isSemisimple.isConnectedReductive
      j hj
    let CC := CentralizerDatum.ofValuationComparison hcomparison
      P.zeroDatum.isSimplyConnectedDerivedCover.isSimplyConnectedCover.isSimplyConnected.isSemisimple.isConnectedReductive
      k hk
    exact ⟨{
      building :=
        P.derivedCoverValuationBuildingData e c j k f hj hk hA h h' hf.isIsogeny hc CD CC
      normalizerHom :=
        P.derivedCoverNormalizerMap e c j k f hj hk hA h h' hf.isIsogeny hc
      apartmentEquiv :=
        P.derivedCoverSourceAffineEquiv e c j k f hj hk hA h h' hf.isIsogeny hc CD CC
      transportedRoots_eq :=
        P.transportedRoots_derivedCoverSource e c j k f hj hk hA h h' hf.isIsogeny hc CD CC
      equivariant :=
        P.derivedCoverSourceAffineEquiv_smul e c j k f hj hk hA h h' hf.isIsogeny hc CD CC
      lifts :=
        P.exists_derivedCoverNormalizer_lift e c j k f hj hk hA h h' hf.isIsogeny hc
      normalizerHom_coe :=
        P.derivedCoverNormalizerMap_coe e c j k f hj hk hA h h' hf.isIsogeny hc
    }⟩

namespace DerivedCoverSourceData

variable {P} (D : P.DerivedCoverSourceData)

/-- The assembled actual comparison reduces the target equality to the exact
facet-fixing and actual opposite-pair prerequisites. -/
theorem normalizer_map_eq_affineWeylGroup
    (hfix : SimplyConnectedFacetFixingStatement.{u})
    (hsourcePairs : RelativeRoot.HasOppositeFactorPairs D.building.i)
    (hApt : P.SatisfiesApartmentAxioms)
    (htargetPairs : RelativeRoot.HasOppositeFactorPairs P.i) :
    (P.simplyConnectedImage.subgroupOf (normalizerPoints P.i)).map
        P.apartment.normalizerAffineEquiv =
      AffineRootSystem.affineWeylGroup P.affineRoots := by
  have : Smooth G.X.hom := P.isConnectedReductive.smooth
  exact P.simplyConnectedNormalizer_map_eq_affineWeylGroup_of_comparison
    D.building D.normalizerHom D.apartmentEquiv D.transportedRoots_eq D.equivariant D.lifts
    hfix P.zeroDatum.isSimplyConnectedDerivedCover.isSimplyConnectedCover.isSimplyConnected
    hsourcePairs hApt htargetPairs

end DerivedCoverSourceData

end Langlands.Geometry.Building.ParahoricBuildingData
