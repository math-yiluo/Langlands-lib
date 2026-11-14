import Langlands.Geometry.Building.IntegerValuationCoverBuildingComparison
import Langlands.Geometry.Building.CentralizerDatumConstruction
import Langlands.BruhatTits.Cartan.CentralizerValuationComparisonProof
import Langlands.GroupScheme.SimplyConnected.DerivedCoverSplitTorusProof
import Langlands.GroupScheme.Derived.CentralSplitTorusProductProof
import Langlands.GroupScheme.Rational.SplitComponentProof
import Langlands.GroupScheme.Rational.SplitCentralEmbedding

/-! # Unconditional source building for an integer-valued derived cover -/

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1000000
universe u
open CategoryTheory AlgebraicGeometry
open scoped CategoryTheory.MonObj
open Langlands.GroupScheme Langlands.BruhatTits

namespace Langlands.Geometry.Building.CentralizerDatum

/-- The actual centralizer and its restriction-evaluation comparison over any field. -/
def ofMaximalSplitTorus {F : Type u} [Field F]
    {G : GroupScheme (Spec (CommRingCat.of F))}
    {S : CommGroupScheme (Spec (CommRingCat.of F))}
    (hG : IsConnectedReductive G) (i : S.toGrp ⟶ G)
    (hi : IsMaximalSplitTorus i) : CentralizerDatum i :=
  Classical.choice <| by
    obtain ⟨Z, j, hj, hjc⟩ :=
      fieldCentralizerRepresentability F S G hi.1.1.isAffineHom i
    let s := torusCentralizerFactor i hj
    have hs : s ≫ j = i := torusCentralizerFactor_comp i hj
    exact ⟨{
      Z := Z
      j := j
      s := s
      isClosedSubgroup := hjc
      isRepresentedBy := hj
      comp_eq := hs
      bijective := Cartan.restrictionEvaluation_bijective_of_torusCentralizer hG hi hjc hj hs
    }⟩

end Langlands.Geometry.Building.CentralizerDatum

namespace Langlands.Geometry.Building.IntegerValuationBuildingData

variable {F : Type u} [Field F]
    {v : Valuation F (WithZero (Multiplicative ℤ))}
    {G D C : GroupScheme (Spec (CommRingCat.of F))}
    [IsAffineHom G.X.hom] [IsAffineHom C.X.hom]
    (B : IntegerValuationBuildingData v G) {d : D ⟶ G} {π : C ⟶ D}

/-- Actual source building, root and action comparisons, and normalizer lifts
for the supplied derived cover over an integer-valued field. -/
structure DerivedCoverSourceData where
  building : IntegerValuationBuildingData v C
  normalizerHom : normalizerPoints building.i →* normalizerPoints B.i
  apartmentEquiv : building.Apartment ≃ᵃ[ℝ] B.Apartment
  transportedRoots_eq :
    AffineRootSystem.transportedRoots apartmentEquiv building.affineRoots = B.affineRoots
  equivariant : ∀ (n : normalizerPoints building.i) (x : building.Apartment),
    apartmentEquiv (n • x) = normalizerHom n • apartmentEquiv x
  lifts : ∀ n : normalizerPoints B.i,
    n ∈ (simplyConnectedImage d π).subgroupOf (normalizerPoints B.i) →
      ∃ m : normalizerPoints building.i, normalizerHom m = n
  normalizerHom_coe : ∀ n : normalizerPoints building.i,
    (normalizerHom n : rationalPoints G) = rationalPoints.map (π ≫ d) n.val

/-- Construct every source and comparison field using the published arbitrary-field
structural theorems and full V6 pullback. -/
def derivedCoverSourceData (hcover : IsSimplyConnectedDerivedCover d π) :
    B.DerivedCoverSourceData (d := d) (π := π) :=
  Classical.choice <| by
    have : Smooth G.X.hom := B.isConnectedReductive.smooth
    have : IsAffineHom D.X.hom :=
      hcover.isSimplyConnectedCover.isSemisimple.isConnectedReductive.isAffineHom
    have : Smooth D.X.hom :=
      hcover.isSimplyConnectedCover.isSemisimple.isConnectedReductive.smooth
    have : Smooth C.X.hom :=
      hcover.isSimplyConnectedCover.isSimplyConnected.isSemisimple.isConnectedReductive.smooth
    have : IsClosedImmersion d.hom.hom.left := hcover.isDerivedSubgroup.1
    have : Mono d.hom.hom.left := inferInstance
    obtain ⟨T, j, e, hj, he, h, U, k, f, hk, h', hf, -⟩ :=
      simplyConnectedDerivedCoverSplitTorus F G D C d π
        hcover B.S B.i B.isMaximalSplitTorus
    obtain ⟨A, a, ha⟩ := (splitComponentStatement F G B.isConnectedReductive).1
    obtain ⟨c, hca, -, -⟩ :=
      ha.exists_commFactor_of_isMaximalSplitTorus B.isMaximalSplitTorus
    have hp : IsCentralIsogeny (RelativeRoot.centralComplementProduct e c) :=
      derivedCentralSplitTorusProduct F G D d B.isConnectedReductive hcover.isDerivedSubgroup
        B.S T A B.i j e a c B.isMaximalSplitTorus hj he h ha hca
    have : Flat (RelativeRoot.centralComplementProduct e c).hom.hom.left := hp.flat
    have : Surjective (RelativeRoot.centralComplementProduct e c).hom.hom.left := hp.surjective
    have : Mono j.hom.hom.left := mono_of_isMaximalSplitTorus hj
    have : Mono k.hom.hom.left := mono_of_isMaximalSplitTorus hk
    have hA : IsSplitTorus A.toGrp := ha.isCentralSplitTorus.1.1
    have hc : IsCentral (CommGroupScheme.groupHom c ≫ B.i) := by
      rw [hca]
      exact ha.isCentralSplitTorus.2
    let CD := CentralizerDatum.ofMaximalSplitTorus
      hcover.isSimplyConnectedCover.isSemisimple.isConnectedReductive j hj
    let CC := CentralizerDatum.ofMaximalSplitTorus
      hcover.isSimplyConnectedCover.isSimplyConnected.isSemisimple.isConnectedReductive k hk
    exact ⟨{
      building :=
        B.derivedCoverValuationBuildingData hcover e c j k f hj hk hA h h' hf.isIsogeny hc CD CC
      normalizerHom :=
        B.derivedCoverNormalizerMap e c j k f hj hk hA h h' hf.isIsogeny hc
      apartmentEquiv :=
        B.derivedCoverSourceAffineEquiv hcover e c j k f hj hk hA h h' hf.isIsogeny hc CD CC
      transportedRoots_eq :=
        B.transportedRoots_derivedCoverSource hcover e c j k f hj hk hA h h' hf.isIsogeny hc CD CC
      equivariant :=
        B.derivedCoverSourceAffineEquiv_smul hcover e c j k f hj hk hA h h' hf.isIsogeny hc CD CC
      lifts :=
        B.exists_derivedCoverNormalizer_lift hcover e c j k f hj hk hA h h' hf.isIsogeny hc
      normalizerHom_coe :=
        B.derivedCoverNormalizerMap_coe e c j k f hj hk hA h h' hf.isIsogeny hc
    }⟩

end Langlands.Geometry.Building.IntegerValuationBuildingData
