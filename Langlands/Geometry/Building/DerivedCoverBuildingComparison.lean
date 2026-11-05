import Langlands.Geometry.Building.DerivedCentralizer
import Langlands.Geometry.Building.DerivedAffineRoots
import Langlands.Geometry.Building.CentralIsogenyAffineRoots
import Langlands.Geometry.Building.SimplyConnectedNormalizerCoverTransport

/-! # Actual source building and comparisons for the supplied derived cover -/

noncomputable section

set_option backward.isDefEq.respectTransparency false

universe u

open CategoryTheory AlgebraicGeometry
open scoped CategoryTheory.MonObj
open Langlands.GroupScheme Langlands.GroupScheme.RealTorusSpace

namespace Langlands.Geometry.Building.ParahoricBuildingData

variable {F : Type u} [Field F] [ValuativeRel F] [TopologicalSpace F]
    [IsNonarchimedeanLocalField F]
    {G : GroupScheme (Spec (CommRingCat.of F))} [IsAffineHom G.X.hom] [Smooth G.X.hom]
    (P : ParahoricBuildingData G)

local instance : IsAffineHom P.zeroDatum.D.X.hom :=
  P.zeroDatum.isSimplyConnectedDerivedCover.isSimplyConnectedCover.isSemisimple.isConnectedReductive.isAffineHom

local instance : Smooth P.zeroDatum.D.X.hom :=
  P.zeroDatum.isSimplyConnectedDerivedCover.isSimplyConnectedCover.isSemisimple.isConnectedReductive.smooth

local instance : IsAffineHom P.zeroDatum.C.X.hom :=
  P.zeroDatum.isSimplyConnectedDerivedCover.isSimplyConnectedCover.isSimplyConnected.isSemisimple.isConnectedReductive.isAffineHom

local instance : Smooth P.zeroDatum.C.X.hom :=
  P.zeroDatum.isSimplyConnectedDerivedCover.isSimplyConnectedCover.isSimplyConnected.isSemisimple.isConnectedReductive.smooth

local instance : Mono P.zeroDatum.d.hom.hom.left := by
  have : IsClosedImmersion P.zeroDatum.d.hom.hom.left :=
    P.zeroDatum.isSimplyConnectedDerivedCover.isDerivedSubgroup.1
  infer_instance

variable {T A U : CommGroupScheme (Spec (CommRingCat.of F))}
    (e : T ⟶ P.S) (c : A ⟶ P.S)
    (j : T.toGrp ⟶ P.zeroDatum.D) (k : U.toGrp ⟶ P.zeroDatum.C)
    (f : U ⟶ T) (hj : IsMaximalSplitTorus j) (hk : IsMaximalSplitTorus k)
    (hA : IsSplitTorus A.toGrp)
    (h : j ≫ P.zeroDatum.d = CommGroupScheme.groupHom e ≫ P.i)
    (h' : k ≫ P.zeroDatum.π = CommGroupScheme.groupHom f ≫ j)
    (hf : IsIsogeny (CommGroupScheme.groupHom f))
    [Flat (RelativeRoot.centralComplementProduct e c).hom.hom.left]
    [Surjective (RelativeRoot.centralComplementProduct e c).hom.hom.left]
    (hc : IsCentral (CommGroupScheme.groupHom c ≫ P.i))

variable [Mono j.hom.hom.left] [Mono k.hom.hom.left]

private abbrev derivedClass : KPApartmentData j (localFieldOrder F) :=
  P.apartment.derivedPullback e c j P.i P.zeroDatum.d
    P.zeroDatum.isSimplyConnectedDerivedCover.isDerivedSubgroup h
    hj.1.1 P.isMaximalSplitTorus.1.1 hA hc P.isMaximalSplitTorus

/-- The entire actual source apartment obtained by the two original
valuation pullbacks for the cover stored in `P`. -/
abbrev derivedCoverApartment : KPApartmentData k (localFieldOrder F) :=
  (P.derivedClass e c j hj hA h hc).centralIsogenyPullback
    P.zeroDatum.π P.zeroDatum.isSimplyConnectedDerivedCover.isSimplyConnectedCover.isCentralIsogeny
    hk.1.1 hj.1.1 f h' hf

variable (CD : CentralizerDatum j) (CC : CentralizerDatum k)

/-- Construct the actual source valuation-building data, including all
original V0–V6 fields, from the supplied structural tori and actual centralizers. -/
def derivedCoverValuationBuildingData : ValuationBuildingData P.zeroDatum.C where
  isConnectedReductive :=
    P.zeroDatum.isSimplyConnectedDerivedCover.isSimplyConnectedCover.isSimplyConnected.isSemisimple.isConnectedReductive
  S := U
  i := k
  isMaximalSplitTorus := hk
  apartment := P.derivedCoverApartment e c j k f hj hk hA h h' hf hc
  centralizer := CC
  isOmegaCompatible := by
    have hD : (P.derivedClass e c j hj hA h hc).IsOmegaCompatible CD :=
      P.isOmegaCompatible.derivedPullback e c j P.i P.zeroDatum.d h
        hj.1.1 hA hc CD P.centralizer
        P.zeroDatum.isSimplyConnectedDerivedCover.isDerivedSubgroup P.isMaximalSplitTorus.1.1
        P.isMaximalSplitTorus
    exact hD.centralIsogenyPullback P.zeroDatum.π f h' hf CC CD
      P.zeroDatum.isSimplyConnectedDerivedCover.isSimplyConnectedCover.isCentralIsogeny
      hk.1.1 hj.1.1

/-- The literal two-stage point pullback is an affine equivalence. -/
def derivedCoverApartmentAffineEquiv :
    P.Apartment ≃ᵃ[ℝ] (P.derivedCoverApartment e c j k f hj hk hA h h' hf hc).Apartment :=
  (P.apartment.derivedApartmentAffineEquiv e c j P.i P.zeroDatum.d
    P.zeroDatum.isSimplyConnectedDerivedCover.isDerivedSubgroup h
    hj.1.1 P.isMaximalSplitTorus.1.1 hA hc P.isMaximalSplitTorus).trans
      ((P.derivedClass e c j hj hA h hc).centralIsogenyApartmentAffineEquiv
        P.zeroDatum.π P.zeroDatum.isSimplyConnectedDerivedCover.isSimplyConnectedCover.isCentralIsogeny
        hk.1.1 hj.1.1 f h' hf)

/-- Every actual cover normalizer maps forward by the original ambient
composite of the cover and derived inclusion. -/
def derivedCoverNormalizerMap : normalizerPoints k →* normalizerPoints P.i :=
  (DerivedNormalizerMap.normalizerPointsHom e c j P.i P.zeroDatum.d h
    hj.1.1 hA P.isMaximalSplitTorus hc).comp
      (splitTorusIsogenyNormalizerMap P.zeroDatum.π hk.1.1 hj.1.1 f h' hf)

omit [Smooth G.X.hom] [Mono k.hom.hom.left] in
@[simp] theorem derivedCoverNormalizerMap_coe (n : normalizerPoints k) :
    (P.derivedCoverNormalizerMap e c j k f hj hk hA h h' hf hc n : rationalPoints G) =
      rationalPoints.map (P.zeroDatum.π ≫ P.zeroDatum.d) n.val := by
  simp only [derivedCoverNormalizerMap, MonoidHom.comp_apply,
    DerivedNormalizerMap.normalizerPointsHom_coe, splitTorusIsogenyNormalizerMap_coe,
    rationalPoints.map_apply, Grp.comp_hom_hom, Category.assoc]

/-- The actual two-stage affine map intertwines all original source normalizers. -/
theorem derivedCoverApartmentAffineEquiv_smul
    (n : normalizerPoints k) (x : P.Apartment) :
    P.derivedCoverApartmentAffineEquiv e c j k f hj hk hA h h' hf hc
        (P.derivedCoverNormalizerMap e c j k f hj hk hA h h' hf hc n • x) =
      n • P.derivedCoverApartmentAffineEquiv e c j k f hj hk hA h h' hf hc x := by
  change
    (P.derivedClass e c j hj hA h hc).centralIsogenyApartmentEquiv
        P.zeroDatum.π P.zeroDatum.isSimplyConnectedDerivedCover.isSimplyConnectedCover.isCentralIsogeny
        hk.1.1 hj.1.1 f h' hf
        (P.apartment.derivedApartmentEquiv e c j P.i P.zeroDatum.d
          P.zeroDatum.isSimplyConnectedDerivedCover.isDerivedSubgroup h
          hj.1.1 P.isMaximalSplitTorus.1.1 hA hc P.isMaximalSplitTorus
          (DerivedNormalizerMap.normalizerPointsHom e c j P.i P.zeroDatum.d h
            hj.1.1 hA P.isMaximalSplitTorus hc
              (splitTorusIsogenyNormalizerMap P.zeroDatum.π hk.1.1 hj.1.1 f h' hf n) • x)) = _
  rw [P.apartment.derivedApartmentEquiv_smul e c j P.i P.zeroDatum.d
      P.zeroDatum.isSimplyConnectedDerivedCover.isDerivedSubgroup h
      hj.1.1 P.isMaximalSplitTorus.1.1 hA hc P.isMaximalSplitTorus,
    (P.derivedClass e c j hj hA h hc).centralIsogenyApartmentEquiv_smul
      P.zeroDatum.π P.zeroDatum.isSimplyConnectedDerivedCover.isSimplyConnectedCover.isCentralIsogeny
      hk.1.1 hj.1.1 f h' hf]
  rfl

private theorem transportedRoots_trans
    {V W X B E H : Type u} [AddCommGroup V] [Module ℝ V] [AddTorsor V B]
    [AddCommGroup W] [Module ℝ W] [AddTorsor W E]
    [AddCommGroup X] [Module ℝ X] [AddTorsor X H]
    (a : B ≃ᵃ[ℝ] E) (b : E ≃ᵃ[ℝ] H) (Ψ : Set (B →ᵃ[ℝ] ℝ)) :
    AffineRootSystem.transportedRoots (a.trans b) Ψ =
      AffineRootSystem.transportedRoots b (AffineRootSystem.transportedRoots a Ψ) := by
  simp only [AffineRootSystem.transportedRoots, Set.image_image]
  congr 1

/-- The two literal transports give exactly the original source affine roots. -/
theorem transportedRoots_derivedCoverApartment :
    AffineRootSystem.transportedRoots
        (P.derivedCoverApartmentAffineEquiv e c j k f hj hk hA h h' hf hc) P.affineRoots =
      (P.derivedCoverApartment e c j k f hj hk hA h h' hf hc).affineRoots := by
  rw [derivedCoverApartmentAffineEquiv, transportedRoots_trans,
    P.apartment.transportedRoots_derivedPullback e c j P.i P.zeroDatum.d
      P.zeroDatum.isSimplyConnectedDerivedCover.isDerivedSubgroup h
      hj.1.1 P.isMaximalSplitTorus.1.1 hA hc P.isMaximalSplitTorus]
  exact (P.derivedClass e c j hj hA h hc).transportedRoots_centralIsogenyPullback
    P.zeroDatum.π P.zeroDatum.isSimplyConnectedDerivedCover.isSimplyConnectedCover.isCentralIsogeny
    hk.1.1 hj.1.1 f h' hf

include h h' in
omit [Smooth G.X.hom] [Mono k.hom.hom.left] in
/-- Every normalizer in the actual simply connected image has an actual
source normalizer preimage under the constructed forward map. -/
theorem exists_derivedCoverNormalizer_lift (n : normalizerPoints P.i)
    (hn : n ∈ P.simplyConnectedImage.subgroupOf (normalizerPoints P.i)) :
    ∃ m : normalizerPoints k,
      P.derivedCoverNormalizerMap e c j k f hj hk hA h h' hf hc m = n := by
  have hcomp : k ≫ P.zeroDatum.π ≫ P.zeroDatum.d =
      CommGroupScheme.groupHom (f ≫ e) ≫ P.i := by
    rw [← Category.assoc, h', Category.assoc, h]
    rfl
  have hn' : n.val ∈ (rationalPoints.map (P.zeroDatum.π ≫ P.zeroDatum.d)).range := hn
  obtain ⟨m, hm⟩ := DerivedCoverNormalizerLift.exists_normalizer_lift
    P.zeroDatum.π P.zeroDatum.d
    P.zeroDatum.isSimplyConnectedDerivedCover.isSimplyConnectedCover.isCentralIsogeny
    k hk P.i (f ≫ e) hcomp n hn'
  exact ⟨m, Subtype.ext ((P.derivedCoverNormalizerMap_coe e c j k f hj hk hA h h' hf hc m).trans hm)⟩

/-- The actual source valuation-building apartment maps back to the original
ambient apartment by the inverse of literal pullback. -/
def derivedCoverSourceAffineEquiv :
    (P.derivedCoverValuationBuildingData e c j k f hj hk hA h h' hf hc CD CC).Apartment ≃ᵃ[ℝ]
      P.Apartment :=
  (P.derivedCoverApartmentAffineEquiv e c j k f hj hk hA h h' hf hc).symm

/-- The constructed comparison intertwines the original source and target
normalizer actions in the direction used by the cover transport theorem. -/
theorem derivedCoverSourceAffineEquiv_smul (n : normalizerPoints k)
    (x : (P.derivedCoverValuationBuildingData e c j k f hj hk hA h h' hf hc CD CC).Apartment) :
    P.derivedCoverSourceAffineEquiv e c j k f hj hk hA h h' hf hc CD CC (n • x) =
      P.derivedCoverNormalizerMap e c j k f hj hk hA h h' hf hc n •
        P.derivedCoverSourceAffineEquiv e c j k f hj hk hA h h' hf hc CD CC x := by
  apply (P.derivedCoverApartmentAffineEquiv e c j k f hj hk hA h h' hf hc).injective
  change
    P.derivedCoverApartmentAffineEquiv e c j k f hj hk hA h h' hf hc
        ((P.derivedCoverApartmentAffineEquiv e c j k f hj hk hA h h' hf hc).symm (n • x)) =
      P.derivedCoverApartmentAffineEquiv e c j k f hj hk hA h h' hf hc
        (P.derivedCoverNormalizerMap e c j k f hj hk hA h h' hf hc n •
          (P.derivedCoverApartmentAffineEquiv e c j k f hj hk hA h h' hf hc).symm x)
  rw [AffineEquiv.apply_symm_apply,
    P.derivedCoverApartmentAffineEquiv_smul e c j k f hj hk hA h h' hf hc,
    AffineEquiv.apply_symm_apply]

/-- Source roots transport to exactly the original ambient affine roots. -/
theorem transportedRoots_derivedCoverSource :
    AffineRootSystem.transportedRoots
        (P.derivedCoverSourceAffineEquiv e c j k f hj hk hA h h' hf hc CD CC)
        (P.derivedCoverValuationBuildingData e c j k f hj hk hA h h' hf hc CD CC).affineRoots =
      P.affineRoots := by
  change AffineRootSystem.transportedRoots
      (P.derivedCoverApartmentAffineEquiv e c j k f hj hk hA h h' hf hc).symm
      (P.derivedCoverApartment e c j k f hj hk hA h h' hf hc).affineRoots = _
  rw [← P.transportedRoots_derivedCoverApartment e c j k f hj hk hA h h' hf hc,
    AffineRootSystem.transportedRoots_symm]

include e c j f hj hk hA h h' hf hc CD CC in
/-- All actual comparison and lifting hypotheses of the existing cover
transport theorem are discharged by the supplied structural data. The exact
facet-fixing and opposite-pair prerequisites remain explicit. -/
theorem normalizer_map_eq_affineWeylGroup_of_derivedCoverData
    (hfix : SimplyConnectedFacetFixingStatement.{u})
    (hFB : RelativeRoot.HasOppositeFactorPairs k)
    (hApt : P.SatisfiesApartmentAxioms)
    (hFP : RelativeRoot.HasOppositeFactorPairs P.i) :
    (P.simplyConnectedImage.subgroupOf (normalizerPoints P.i)).map
        P.apartment.normalizerAffineEquiv =
      AffineRootSystem.affineWeylGroup P.affineRoots :=
  P.simplyConnectedNormalizer_map_eq_affineWeylGroup_of_comparison
    (P.derivedCoverValuationBuildingData e c j k f hj hk hA h h' hf hc CD CC)
    (P.derivedCoverNormalizerMap e c j k f hj hk hA h h' hf hc)
    (P.derivedCoverSourceAffineEquiv e c j k f hj hk hA h h' hf hc CD CC)
    (P.transportedRoots_derivedCoverSource e c j k f hj hk hA h h' hf hc CD CC)
    (P.derivedCoverSourceAffineEquiv_smul e c j k f hj hk hA h h' hf hc CD CC)
    (P.exists_derivedCoverNormalizer_lift e c j k f hj hk hA h h' hf hc)
    hfix P.zeroDatum.isSimplyConnectedDerivedCover.isSimplyConnectedCover.isSimplyConnected
    hFB hApt hFP

end Langlands.Geometry.Building.ParahoricBuildingData
