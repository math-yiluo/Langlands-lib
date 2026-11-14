import Langlands.Geometry.Building.DerivedCentralizer
import Langlands.Geometry.Building.DerivedAffineRoots
import Langlands.Geometry.Building.CentralIsogenyAffineRoots
import Langlands.Geometry.Building.IntegerValuationCoverCentralizer
import Langlands.Geometry.Building.IntegerValuationBuildingData
import Langlands.GroupScheme.Rational.DerivedCoverNormalizerLift
import Langlands.Geometry.Building.AffineRootSystemTransport
import Langlands.Geometry.Building.KPZeroSubgroups

/-! # Actual source building and comparisons for the supplied derived cover -/

noncomputable section

set_option backward.isDefEq.respectTransparency false

universe u

open CategoryTheory AlgebraicGeometry
open scoped CategoryTheory.MonObj
open Langlands.GroupScheme Langlands.GroupScheme.RealTorusSpace

namespace Langlands.Geometry.Building.IntegerValuationBuildingData

variable {F : Type u} [Field F]
    {v : Valuation F (WithZero (Multiplicative ℤ))}
    {G D C : GroupScheme (Spec (CommRingCat.of F))} [IsAffineHom G.X.hom]
    (B : IntegerValuationBuildingData v G)
    {d : D ⟶ G} {π : C ⟶ D} (hcover : IsSimplyConnectedDerivedCover d π)

variable [Smooth G.X.hom]
    [IsAffineHom D.X.hom] [Smooth D.X.hom]
    [IsAffineHom C.X.hom] [Smooth C.X.hom]
    [Mono d.hom.hom.left]

variable {T A U : CommGroupScheme (Spec (CommRingCat.of F))}
    (e : T ⟶ B.S) (c : A ⟶ B.S)
    (j : T.toGrp ⟶ D) (k : U.toGrp ⟶ C)
    (f : U ⟶ T) (hj : IsMaximalSplitTorus j) (hk : IsMaximalSplitTorus k)
    (hA : IsSplitTorus A.toGrp)
    (h : j ≫ d = CommGroupScheme.groupHom e ≫ B.i)
    (h' : k ≫ π = CommGroupScheme.groupHom f ≫ j)
    (hf : IsIsogeny (CommGroupScheme.groupHom f))
    [Flat (RelativeRoot.centralComplementProduct e c).hom.hom.left]
    [Surjective (RelativeRoot.centralComplementProduct e c).hom.hom.left]
    (hc : IsCentral (CommGroupScheme.groupHom c ≫ B.i))

variable [Mono j.hom.hom.left] [Mono k.hom.hom.left]

private abbrev derivedClass : KPApartmentData j (IntegerValuation.order v) :=
  B.apartment.derivedPullback e c j B.i d
    hcover.isDerivedSubgroup h
    hj.1.1 B.isMaximalSplitTorus.1.1 hA hc B.isMaximalSplitTorus

/-- The entire actual source apartment obtained by the two original
valuation pullbacks for the supplied cover. -/
abbrev derivedCoverApartment : KPApartmentData k (IntegerValuation.order v) :=
  (B.derivedClass hcover e c j hj hA h hc).centralIsogenyPullback
    π hcover.isSimplyConnectedCover.isCentralIsogeny
    hk.1.1 hj.1.1 f h' hf

variable (CD : CentralizerDatum j) (CC : CentralizerDatum k)

/-- Construct the actual source valuation-building data, including all
original V0–V6 fields, from the supplied structural tori and actual centralizers. -/
def derivedCoverValuationBuildingData : IntegerValuationBuildingData v C where
  isConnectedReductive :=
    hcover.isSimplyConnectedCover.isSimplyConnected.isSemisimple.isConnectedReductive
  S := U
  i := k
  isMaximalSplitTorus := hk
  apartment := B.derivedCoverApartment hcover e c j k f hj hk hA h h' hf hc
  centralizer := CC
  isOmegaCompatible := by
    have hD : IntegerValuation.IsOmegaCompatible v
        (B.derivedClass hcover e c j hj hA h hc) CD :=
      B.isOmegaCompatible.derivedPullback v e c j B.i d h
        hj.1.1 hA hc CD B.centralizer
        hcover.isDerivedSubgroup B.isMaximalSplitTorus.1.1
        B.isMaximalSplitTorus
    exact hD.centralIsogenyPullback v π f h' hf CC CD
      hcover.isSimplyConnectedCover.isCentralIsogeny
      hk.1.1 hj.1.1

/-- The literal two-stage point pullback is an affine equivalence. -/
def derivedCoverApartmentAffineEquiv :
    B.Apartment ≃ᵃ[ℝ] (B.derivedCoverApartment hcover e c j k f hj hk hA h h' hf hc).Apartment :=
  (B.apartment.derivedApartmentAffineEquiv e c j B.i d
    hcover.isDerivedSubgroup h
    hj.1.1 B.isMaximalSplitTorus.1.1 hA hc B.isMaximalSplitTorus).trans
      ((B.derivedClass hcover e c j hj hA h hc).centralIsogenyApartmentAffineEquiv
        π hcover.isSimplyConnectedCover.isCentralIsogeny
        hk.1.1 hj.1.1 f h' hf)

/-- Every actual cover normalizer maps forward by the original ambient
composite of the cover and derived inclusion. -/
def derivedCoverNormalizerMap : normalizerPoints k →* normalizerPoints B.i :=
  (DerivedNormalizerMap.normalizerPointsHom e c j B.i d h
    hj.1.1 hA B.isMaximalSplitTorus hc).comp
      (splitTorusIsogenyNormalizerMap π hk.1.1 hj.1.1 f h' hf)

omit [Mono k.hom.hom.left] [Smooth G.X.hom]
    [IsAffineHom D.X.hom] [Smooth D.X.hom]
    [IsAffineHom C.X.hom] [Smooth C.X.hom] [Mono d.hom.hom.left] in
@[simp] theorem derivedCoverNormalizerMap_coe (n : normalizerPoints k) :
    (B.derivedCoverNormalizerMap e c j k f hj hk hA h h' hf hc n : rationalPoints G) =
      rationalPoints.map (π ≫ d) n.val := by
  simp only [derivedCoverNormalizerMap, MonoidHom.comp_apply,
    DerivedNormalizerMap.normalizerPointsHom_coe, splitTorusIsogenyNormalizerMap_coe,
    rationalPoints.map_apply, Grp.comp_hom_hom, Category.assoc]

omit [Mono d.hom.hom.left] in
/-- The actual two-stage affine map intertwines all original source normalizers. -/
theorem derivedCoverApartmentAffineEquiv_smul
    (n : normalizerPoints k) (x : B.Apartment) :
    B.derivedCoverApartmentAffineEquiv hcover e c j k f hj hk hA h h' hf hc
        (B.derivedCoverNormalizerMap e c j k f hj hk hA h h' hf hc n • x) =
      n • B.derivedCoverApartmentAffineEquiv hcover e c j k f hj hk hA h h' hf hc x := by
  change
    (B.derivedClass hcover e c j hj hA h hc).centralIsogenyApartmentEquiv
        π hcover.isSimplyConnectedCover.isCentralIsogeny
        hk.1.1 hj.1.1 f h' hf
        (B.apartment.derivedApartmentEquiv e c j B.i d
          hcover.isDerivedSubgroup h
          hj.1.1 B.isMaximalSplitTorus.1.1 hA hc B.isMaximalSplitTorus
          (DerivedNormalizerMap.normalizerPointsHom e c j B.i d h
            hj.1.1 hA B.isMaximalSplitTorus hc
              (splitTorusIsogenyNormalizerMap π hk.1.1 hj.1.1 f h' hf n) • x)) = _
  rw [B.apartment.derivedApartmentEquiv_smul e c j B.i d
      hcover.isDerivedSubgroup h
      hj.1.1 B.isMaximalSplitTorus.1.1 hA hc B.isMaximalSplitTorus,
    (B.derivedClass hcover e c j hj hA h hc).centralIsogenyApartmentEquiv_smul
      π hcover.isSimplyConnectedCover.isCentralIsogeny
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

omit [Mono d.hom.hom.left] in
/-- The two literal transports give exactly the original source affine roots. -/
theorem transportedRoots_derivedCoverApartment :
    AffineRootSystem.transportedRoots
        (B.derivedCoverApartmentAffineEquiv hcover e c j k f hj hk hA h h' hf hc) B.affineRoots =
      (B.derivedCoverApartment hcover e c j k f hj hk hA h h' hf hc).affineRoots := by
  rw [derivedCoverApartmentAffineEquiv, transportedRoots_trans,
    B.apartment.transportedRoots_derivedPullback e c j B.i d
      hcover.isDerivedSubgroup h
      hj.1.1 B.isMaximalSplitTorus.1.1 hA hc B.isMaximalSplitTorus]
  exact (B.derivedClass hcover e c j hj hA h hc).transportedRoots_centralIsogenyPullback
    π hcover.isSimplyConnectedCover.isCentralIsogeny
    hk.1.1 hj.1.1 f h' hf

include h h' hcover in
omit [Mono k.hom.hom.left] [Smooth G.X.hom]
    [IsAffineHom D.X.hom] [Smooth D.X.hom] [Smooth C.X.hom] in
/-- Every normalizer in the actual simply connected image has an actual
source normalizer preimage under the constructed forward map. -/
theorem exists_derivedCoverNormalizer_lift (n : normalizerPoints B.i)
    (hn : n ∈ (simplyConnectedImage d π).subgroupOf (normalizerPoints B.i)) :
    ∃ m : normalizerPoints k,
      B.derivedCoverNormalizerMap e c j k f hj hk hA h h' hf hc m = n := by
  have hcomp : k ≫ π ≫ d =
      CommGroupScheme.groupHom (f ≫ e) ≫ B.i := by
    rw [← Category.assoc, h', Category.assoc, h]
    rfl
  have hn' : n.val ∈ (rationalPoints.map (π ≫ d)).range := hn
  obtain ⟨m, hm⟩ := DerivedCoverNormalizerLift.exists_normalizer_lift
    π d
    hcover.isSimplyConnectedCover.isCentralIsogeny
    k hk B.i (f ≫ e) hcomp n hn'
  exact ⟨m, Subtype.ext ((B.derivedCoverNormalizerMap_coe e c j k f hj hk hA h h' hf hc m).trans hm)⟩

/-- The actual source valuation-building apartment maps back to the original
ambient apartment by the inverse of literal pullback. -/
def derivedCoverSourceAffineEquiv :
    (B.derivedCoverValuationBuildingData hcover e c j k f hj hk hA h h' hf hc CD CC).Apartment ≃ᵃ[ℝ]
      B.Apartment :=
  (B.derivedCoverApartmentAffineEquiv hcover e c j k f hj hk hA h h' hf hc).symm

omit [Mono d.hom.hom.left] in
/-- The constructed comparison intertwines the original source and target
normalizer actions in the direction used by the cover transport theorem. -/
theorem derivedCoverSourceAffineEquiv_smul (n : normalizerPoints k)
    (x : (B.derivedCoverValuationBuildingData hcover e c j k f hj hk hA h h' hf hc CD CC).Apartment) :
    B.derivedCoverSourceAffineEquiv hcover e c j k f hj hk hA h h' hf hc CD CC (n • x) =
      B.derivedCoverNormalizerMap e c j k f hj hk hA h h' hf hc n •
        B.derivedCoverSourceAffineEquiv hcover e c j k f hj hk hA h h' hf hc CD CC x := by
  apply (B.derivedCoverApartmentAffineEquiv hcover e c j k f hj hk hA h h' hf hc).injective
  change
    B.derivedCoverApartmentAffineEquiv hcover e c j k f hj hk hA h h' hf hc
        ((B.derivedCoverApartmentAffineEquiv hcover e c j k f hj hk hA h h' hf hc).symm (n • x)) =
      B.derivedCoverApartmentAffineEquiv hcover e c j k f hj hk hA h h' hf hc
        (B.derivedCoverNormalizerMap e c j k f hj hk hA h h' hf hc n •
          (B.derivedCoverApartmentAffineEquiv hcover e c j k f hj hk hA h h' hf hc).symm x)
  rw [AffineEquiv.apply_symm_apply,
    B.derivedCoverApartmentAffineEquiv_smul hcover e c j k f hj hk hA h h' hf hc,
    AffineEquiv.apply_symm_apply]

omit [Mono d.hom.hom.left] in
/-- Source roots transport to exactly the original ambient affine roots. -/
theorem transportedRoots_derivedCoverSource :
    AffineRootSystem.transportedRoots
        (B.derivedCoverSourceAffineEquiv hcover e c j k f hj hk hA h h' hf hc CD CC)
        (B.derivedCoverValuationBuildingData hcover e c j k f hj hk hA h h' hf hc CD CC).affineRoots =
      B.affineRoots := by
  change AffineRootSystem.transportedRoots
      (B.derivedCoverApartmentAffineEquiv hcover e c j k f hj hk hA h h' hf hc).symm
      (B.derivedCoverApartment hcover e c j k f hj hk hA h h' hf hc).affineRoots = _
  rw [← B.transportedRoots_derivedCoverApartment hcover e c j k f hj hk hA h h' hf hc,
    AffineRootSystem.transportedRoots_symm]

end Langlands.Geometry.Building.IntegerValuationBuildingData
