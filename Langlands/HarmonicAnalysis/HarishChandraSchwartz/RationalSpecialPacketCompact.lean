import Langlands.HarmonicAnalysis.HarishChandraSchwartz.RationalWeakExpansionTargets
import Langlands.HarmonicAnalysis.HarishChandraSchwartz.RationalSemistandardConstantTermEstimate
import Langlands.GroupScheme.Rational.SemistandardProperLeviRank
import Langlands.HarmonicAnalysis.HarishChandraSchwartz.RationalSpecialCompactConstantTermPremises
import Langlands.BruhatTits.SpecialCompact.AvailableBasisProof
import Langlands.BruhatTits.SpecialCompact.JointBasisFinalAssembly
import Langlands.BruhatTits.SpecialCompact.MoyPrasadDoubleRootBasis
import Langlands.BruhatTits.SpecialCompact.ParabolicCompactFactorization
import Langlands.Geometry.Building.RootValuationBuildingConstructionProof
import Langlands.Geometry.Building.RootGroupActionAxiomProof
import Langlands.Geometry.Building.FullValidity.DatumTransport.RootSystem
import Langlands.Geometry.Building.KPDoubleRootFiltrationExistence

/-! # The common special compact for the source-normalized packet proof -/

noncomputable section

open CategoryTheory AlgebraicGeometry
open scoped CategoryTheory.MonObj
open Langlands.GroupScheme Langlands.Geometry.Building Langlands.BruhatTits.SpecialCompact
open Langlands.Plancherel Langlands.Plancherel.RenardCartan Langlands.Aubert.General

namespace Langlands.HarishChandraSchwartz

universe u

attribute [local instance]
  DynamicOppositeCanonicalScalar.dynamicOppositeCanonicalScalarIsAffine
  DynamicOppositeCanonicalScalar.dynamicOppositeCanonicalScalarTopologicalSpace

variable {F : Type u} [Field F] [ValuativeRel F] [TopologicalSpace F]
  [IsNonarchimedeanLocalField F]
  {S : CommGroupScheme (Spec (CommRingCat.of F))}
  {G : GroupScheme (Spec (CommRingCat.of F))} [IsAffineHom G.X.hom]
  {i : S.toGrp ⟶ G} (hi : IsMaximalSplitTorus i) (ν : cocharacterLattice S)

/-- One compact at the prescribed torus serves the weighted expansion, the
simultaneous normal basis, and the ambient and Levi Cartan arguments. -/
def HasSpecialPacketCompact : Prop :=
  ∃ L : OpenSubgroup (rationalPoints G), IsCompact (L : Set (rationalPoints G)) ∧
    WeakExpansion.IsSpecialVertexCompact ν hi L ∧
    BruhatTits.Iwasawa.ParabolicPointProductFamily i ν (L : Subgroup (rationalPoints G)) ∧
    SimultaneousStandardBasisAt i ν (L : Subgroup (rationalPoints G)) ∧
    RationalPointFamily.FiniteCartanCovering F i ν (L : Subgroup (rationalPoints G)) ∧
    ∀ J ⊆ simpleRelativeRoots i ν, StandardLeviCartanCovering F i ν J (L : Subgroup (rationalPoints G))

private theorem hasSpecialPacketCompact_of_based
    (V : ValuationBuildingData G) (hS : V.S = S) (hVi : HEq V.i i)
    (hV : ∀ v : cocharacterLattice V.S, IsGenericCocharacter V.i v →
      HasSpecialPacketCompact V.isMaximalSplitTorus v)
    (hν : IsGenericCocharacter i ν) : HasSpecialPacketCompact hi ν := by
  obtain ⟨_, SV, iV, hiV, AV, CV, _⟩ := V
  subst hS
  obtain rfl := eq_of_heq hVi
  have he : hiV = hi := Subsingleton.elim _ _
  exact he ▸ hV ν hν

set_option maxHeartbeats 1800000 in
/-- Keep the validity data of the corrected assignment at the common compact.
All structural data use the same special vertex of its rebased apartment. -/
theorem hasSpecialPacketCompact_of_availability
    (hAvail : BruhatTitsAvailabilityStatement.{u}) (hG : IsConnectedReductive G)
    (hν : IsGenericCocharacter i ν) : HasSpecialPacketCompact hi ν := by
  have : Smooth G.X.hom := hG.smooth
  obtain ⟨B₀, hB₀⟩ := hAvail
  obtain ⟨B, hB, hS, hiB⟩ := validAssignmentTorusRebasing B₀ hB₀ F G hG S i hi
  let V := (B.datum F G hG).base.toValuationBuildingData
  refine hasSpecialPacketCompact_of_based hi ν V hS hiB ?_ hν
  intro v hv
  have hA : B.IsAvailableFor F G hG := hB.isAvailableFor
  obtain ⟨x, hx⟩ := availableSpecialVertexExistence F G hG B hA
  obtain ⟨hP, _, hBasis⟩ := availableSimultaneousStandardBasis F G hG B hB v hv x hx
  obtain ⟨hC, hL⟩ := validSpecialCompactRenardCartanComparison F G hG B hB v hv x hx
  let L : OpenSubgroup (rationalPoints G) := ⟨V.apartment.specialCompactSubgroup x, hP.2.1.2.1⟩
  have hspecial : WeakExpansion.IsSpecialVertexCompact v V.isMaximalSplitTorus L :=
    ⟨V.centralizer, V.apartment, hA.affineRootSystem.apartmentAxioms,
      hA.boundedSubgroups, x, hx, hP, rfl⟩
  exact ⟨L, hP.2.1.1, hspecial,
    ((BruhatTits.Iwasawa.availableIwasawa F G hG B hA v hv).1 x hx).2.2.1,
    hBasis, RationalPointFamily.rationalPositiveCartanCover F G V.S V.i v V.apartment x
      V.centralizer.Z V.centralizer.j V.centralizer.s V.centralizer.bijective
      V.centralizer.isRepresentedBy V.centralizer.comp_eq hC,
    fun J hJ => standardLeviCartanCovering_of_compatibility V.apartment x v
      V.centralizer.isRepresentedBy V.centralizer.comp_eq hL hJ⟩

include hi in
set_option maxHeartbeats 1800000 in
private theorem exists_specialCompactBuildingDataAt (hG : IsConnectedReductive G) :
    ∃ B : ParahoricBuildingData G, B.S = S ∧ HEq B.i i ∧
      B.SatisfiesApartmentAxioms ∧ B.HasBoundedOpenStabilizers ∧
      ∀ x : B.Apartment, B.apartment.IsSpecialApartmentVertex x →
        IsCompactOpenMaximal F (B.apartment.specialCompactSubgroup x) ∧
        ∀ v : cocharacterLattice B.S, IsGenericCocharacter B.i v →
          HasWeylRepresentatives B.i (B.apartment.specialCompactSubgroup x) ∧
          BruhatTits.Iwasawa.ParabolicPointProductFamily B.i v (B.apartment.specialCompactSubgroup x) ∧
          SpecialCompactRenardComparison B.apartment x v
            B.centralizer.j B.centralizer.s B.centralizer.bijective := by
  let : Smooth G.X.hom := hG.smooth
  obtain ⟨V₀, hV₀⟩ := valuationApartmentAxiomsExistence F G hG
  obtain ⟨g, e, he⟩ := (maximalSplitTorusConjugacy F G hG).1
    V₀.S S V₀.i i V₀.isMaximalSplitTorus hi
  let σ : V₀.S ≅ S :=
    { hom := Additive.ofMul e.hom
      inv := Additive.ofMul e.inv
      hom_inv_id := congrArg Additive.ofMul e.hom_inv_id
      inv_hom_id := congrArg Additive.ofMul e.inv_hom_id }
  let V := V₀.basedTransport σ (G.innerIso g) he
  have hV : V.SatisfiesApartmentAxioms :=
    ValuationBuildingData.SatisfiesApartmentAxioms.basedTransport V₀ σ (G.innerIso g) he hV₀
  obtain ⟨B, hB⟩ := ParahoricBuildingData.exists_toValuationBuildingData_eq V
  have hA : B.SatisfiesApartmentAxioms := hB ▸ hV
  obtain ⟨R, T, hbuild, hbound, haffine, hreflections, _, hfacets, htits⟩ :=
    B.fiveAxioms_of_statements hA (actualApartmentSplitting F G B.toValuationBuildingData hA)
      affineIwahoriTits affineIwahoriTitsBuilding
  obtain ⟨hgen, _⟩ := rootGroupActionAxiom F G B hA
  obtain ⟨M⟩ := metricRealization F G B.isConnectedReductive B R T hbuild hbound haffine
    hreflections hA hfacets htits
  have hcommon (x : B.Apartment) :
      B.toValuationBuildingData.HasCommonApartmentWith (B.apartmentMap x) :=
    R.hasCommonApartmentWith_of_isBuilding hbuild.isBuilding _
  refine ⟨B, congrArg ValuationBuildingData.S hB, ?_, hA, hbound, ?_⟩
  · rw [hB]
    rfl
  intro x hx
  have hmax := BruhatTits.Iwasawa.compactOpenMaximal_of_buildingGeometry
    B M hA hbound hfacets.injective hcommon (B.apartment.isSpecialBuildingPoint_apartmentMap hx.1)
  refine ⟨hmax, fun v hv => ?_⟩
  have hle := B.parahoricAt_le_compactStabilizer hA.topologyCompatible x
  have hW : HasWeylRepresentatives B.i (B.apartment.specialCompactSubgroup x) := by
    intro w
    obtain ⟨n, hn, hnw⟩ := WeylRepresentatives.special_parahoric_normalizer_surjective B hA
      hgen (rootRankOneFactorization F G B.isConnectedReductive B.S B.i B.isMaximalSplitTorus)
      v hv hx.1 w
    exact ⟨n, hle hn, hnw⟩
  let : B.normalizerZero.Normal := B.normal_normalizerZero
  have hcartan := BruhatTits.Cartan.parahoricCartanConclusions_of_buildingGeometry B hA
    hgen hbuild.normalizerApartmentStabilizer hfacets.injective htits v hv x hx (hcommon x)
  exact ⟨hW, BruhatTits.Iwasawa.specialCompactParabolicProductFamily B hA hgen v hv x hx,
    specialCompactCartanComparison_of_parahoric B v x hcartan hle hmax.1,
    dominantLattice_of_maximalSplitTorus B.i B.isMaximalSplitTorus v
      B.centralizer.s B.centralizer.bijective⟩

set_option maxHeartbeats 1800000 in
private theorem specialPacketLeviProperties
    (B : ParahoricBuildingData G) (hA : B.SatisfiesApartmentAxioms)
    (v : cocharacterLattice B.S) (hv : IsGenericCocharacter B.i v)
    (x : B.Apartment) (hx : B.apartment.IsSpecialApartmentVertex x)
    (hK : IsCompactOpenMaximal F (B.apartment.specialCompactSubgroup x)) :
    (∀ J ⊆ simpleRelativeRoots B.i v,
      haveI : IsAffineHom (Standard.leviScheme B.i v J).X.hom :=
        (Standard.isClosedSubgroup_leviHom B.i v J).isAffineHom
      IsCompactOpenMaximal F (B.apartment.specialCompactLeviSubgroup v J x)) ∧
    SpecialCompactStandardLeviCompatibility B.apartment x v
      B.centralizer.s B.centralizer.bijective B.centralizer.j := by
  let : Smooth G.X.hom := B.isConnectedReductive.smooth
  have hLevi (J : Set (characterLattice B.S)) (hJ : J ⊆ simpleRelativeRoots B.i v) :
      haveI : IsAffineHom (Standard.leviScheme B.i v J).X.hom :=
        (Standard.isClosedSubgroup_leviHom B.i v J).isAffineHom
      haveI : Mono (Standard.leviTorusHom B.i v J).hom.hom.left :=
        mono_of_isMaximalSplitTorus
          (Standard.isMaximalSplitTorus_leviTorusHom B.i v J B.isMaximalSplitTorus)
      IsCompactOpenMaximal F (B.apartment.specialCompactLeviSubgroup v J x) ∧
        SameCompactLeviCartanComparison B.apartment x v J
          (standardLeviCentralizerDatum B.i B.centralizer v J).j
          B.centralizer.s B.centralizer.bijective := by
    let : IsAffineHom (Standard.leviScheme B.i v J).X.hom :=
      (Standard.isClosedSubgroup_leviHom B.i v J).isAffineHom
    let iM := Standard.leviTorusHom B.i v J
    have hiM : IsMaximalSplitTorus iM :=
      Standard.isMaximalSplitTorus_leviTorusHom B.i v J B.isMaximalSplitTorus
    let : Mono iM.hom.hom.left := mono_of_isMaximalSplitTorus hiM
    have hM := standardLevi_isConnectedReductive B.isConnectedReductive
      B.i B.isMaximalSplitTorus v hv J hJ
    obtain ⟨BM, hSM, hiBM, hAM, _, hMdata⟩ := exists_specialCompactBuildingDataAt hiM hM
    obtain ⟨xM, hxM, heq⟩ := exists_specialCompactLevi_of_buildingGeometry B hA v hv J hJ x hx hK
      BM.i BM.centralizer BM.apartment BM.isOmegaCompatible hAM.topologyCompatible hSM hiBM
      (fun _ _ y hy => (hMdata y hy).1)
    let CM := standardLeviCentralizerDatum B.i B.centralizer v J
    refine ⟨?_, ?_⟩
    · rw [← heq]
      exact (hMdata xM hxM).1
    · exact specialCompactCartanComparison_on_subgroup_of_heq BM.apartment xM
        BM.centralizer CM hSM hiBM _ heq
        (fun vM hvM => ((hMdata xM hxM).2 vM hvM).2.2.1)
        v (BruhatTits.SpecialCompact.isGenericCocharacter_leviTorusHom hv J)
  refine ⟨fun J hJ => (hLevi J hJ).1, fun J hJ => ?_⟩
  let : IsAffineHom (Standard.leviScheme B.i v J).X.hom :=
    (Standard.isClosedSubgroup_leviHom B.i v J).isAffineHom
  let : Mono (Standard.leviTorusHom B.i v J).hom.hom.left :=
    mono_of_isMaximalSplitTorus
      (Standard.isMaximalSplitTorus_leviTorusHom B.i v J B.isMaximalSplitTorus)
  let CM := standardLeviCentralizerDatum B.i B.centralizer v J
  exact ⟨CM.j, CM.isClosedSubgroup, CM.isRepresentedBy,
    standardLeviCentralizerFactor_comp B.i v J B.centralizer.j B.centralizer.isRepresentedBy,
    CM.comp_eq, positiveRelativeRoots_standardLevi_subset B.i v J, (hLevi J hJ).2,
    dominantLattice_standardLevi B.i B.isMaximalSplitTorus v
      B.centralizer.s B.centralizer.bijective J⟩

set_option maxHeartbeats 2400000 in
/-- Choose the common special compact for the packet estimates from
the root-valuation building and the original positive-depth Moy–Prasad basis. -/
def specialPacketCompact (hG : IsConnectedReductive G) (hν : IsGenericCocharacter i ν) :
    {L : OpenSubgroup (rationalPoints G) // IsCompact (L : Set (rationalPoints G)) ∧
      WeakExpansion.IsSpecialVertexCompact ν hi L ∧
      BruhatTits.Iwasawa.ParabolicPointProductFamily i ν L.toSubgroup ∧
      SimultaneousStandardBasisAt i ν L.toSubgroup ∧
      RationalPointFamily.FiniteCartanCovering F i ν L.toSubgroup ∧
      ∀ J ⊆ simpleRelativeRoots i ν, StandardLeviCartanCovering F i ν J L.toSubgroup} := by
  apply Classical.indefiniteDescription
  let : Smooth G.X.hom := hG.smooth
  obtain ⟨B, hS, hiB, hA, hbound, hdata⟩ := exists_specialCompactBuildingDataAt hi hG
  refine hasSpecialPacketCompact_of_based hi ν B.toValuationBuildingData hS hiB ?_ hν
  intro v hv
  have hΨ := hA.isAffineRootSystem_affineRoots
  obtain ⟨x, hx⟩ := hΨ.exists_isSpecialPoint
  have hxs : B.apartment.IsSpecialApartmentVertex x :=
    ⟨hx, AffineRootSystem.isVertex_of_isSpecialPoint hΨ hx⟩
  obtain ⟨hmax, hvertex⟩ := hdata x hxs
  obtain ⟨hW, hI, hC⟩ := hvertex v hv
  have ⟨hLmax, hL⟩ := specialPacketLeviProperties B hA v hv x hxs hmax
  have hfactor := hasParabolicFactorization_of_maximal_compact_levis B.isConnectedReductive
    B.i B.isMaximalSplitTorus v hv (B.apartment.specialCompactSubgroup x) hmax.1 hLmax
  have hP : SpecialCompactProperties F B.i v (B.apartment.specialCompactSubgroup x) :=
    ⟨isBoundedOpenMaximal_of_isCompactOpenMaximal B.isConnectedReductive hmax, hmax, hW, hfactor⟩
  obtain ⟨Zf, hZ, hZo, hZ2⟩ := centralizerFiltrationDoubleRootExistence F G B hA
  have hBasis := simultaneousStandardBasisAt_of_doubleRootFiltration B Zf hA hZ hZ2 hZo
    x v hv hmax.1
  let L : OpenSubgroup (rationalPoints G) := ⟨B.apartment.specialCompactSubgroup x, hmax.2.1⟩
  exact ⟨L, hmax.1, ⟨B.centralizer, B.apartment, hA, hbound, x, hxs, hP, rfl⟩,
    hI, hBasis, RationalPointFamily.rationalPositiveCartanCover F G B.S B.i v B.apartment x
      B.centralizer.Z B.centralizer.j B.centralizer.s B.centralizer.bijective
      B.centralizer.isRepresentedBy B.centralizer.comp_eq hC,
    fun J hJ => standardLeviCartanCovering_of_compatibility B.apartment x v
      B.centralizer.isRepresentedBy B.centralizer.comp_eq hL hJ⟩

/-- The constructed compact supplies the common geometric input to the packet estimates. -/
theorem hasSpecialPacketCompact (hG : IsConnectedReductive G)
    (hν : IsGenericCocharacter i ν) : HasSpecialPacketCompact hi ν :=
  ⟨(specialPacketCompact hi ν hG hν).val, (specialPacketCompact hi ν hG hν).property⟩

section SemistandardTrace

open RationalSemistandard

attribute [local instance] rationalWeightsIsAffine rationalWeightsTopology

omit [IsNonarchimedeanLocalField F] in
private theorem specialCompactProperties_of_heq
    {M : GroupScheme (Spec (CommRingCat.of F))} [IsAffineHom M.X.hom]
    {SM SM' : CommGroupScheme (Spec (CommRingCat.of F))} (hS : SM' = SM)
    {i' : SM'.toGrp ⟶ M} {iM : SM.toGrp ⟶ M} (hi : HEq i' iM)
    (L : Subgroup (rationalPoints M))
    (h : ∀ v : cocharacterLattice SM', IsGenericCocharacter i' v → SpecialCompactProperties F i' v L)
    (v : cocharacterLattice SM) (hv : IsGenericCocharacter iM v) : SpecialCompactProperties F iM v L := by
  subst hS
  obtain rfl := eq_of_heq hi
  exact h v hv

omit [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F] in
private theorem exists_genericCocharacter_heq
    {M : GroupScheme (Spec (CommRingCat.of F))} [IsAffineHom M.X.hom]
    {SM SM' : CommGroupScheme (Spec (CommRingCat.of F))} (hS : SM' = SM)
    {i' : SM'.toGrp ⟶ M} {iM : SM.toGrp ⟶ M} (hi : HEq i' iM)
    (v : cocharacterLattice SM) (hv : IsGenericCocharacter iM v) :
    ∃ w : cocharacterLattice SM', HEq w v ∧ IsGenericCocharacter i' w := by
  subst hS
  obtain rfl := eq_of_heq hi
  exact ⟨v, HEq.rfl, hv⟩

private theorem isSpecialVertexCompact_of_heq
    {M : GroupScheme (Spec (CommRingCat.of F))} [IsAffineHom M.X.hom]
    {SM SM' : CommGroupScheme (Spec (CommRingCat.of F))} (hS : SM' = SM)
    {i' : SM'.toGrp ⟶ M} {iM : SM.toGrp ⟶ M} (hi : HEq i' iM)
    (hi' : IsMaximalSplitTorus i') (hiM : IsMaximalSplitTorus iM)
    {v' : cocharacterLattice SM'} {v : cocharacterLattice SM} (hv : HEq v' v)
    {L : OpenSubgroup (rationalPoints M)}
    (h : WeakExpansion.IsSpecialVertexCompact v' hi' L) :
    WeakExpansion.IsSpecialVertexCompact v hiM L := by
  subst hS
  obtain rfl := eq_of_heq hi
  obtain rfl := eq_of_heq hv
  exact h

set_option maxRecDepth 4096 in
set_option maxHeartbeats 2200000 in
private theorem standardLeviTraceProperties
    (V : ValuationBuildingData G) (hA : V.SatisfiesApartmentAxioms)
    (ξ : cocharacterLattice V.S) (hξ : IsGenericCocharacter V.i ξ)
    (J : Set (characterLattice V.S)) (hJ : J ⊆ simpleRelativeRoots V.i ξ)
    (x : V.Apartment) (hx : V.apartment.IsSpecialApartmentVertex x)
    (hK : IsCompactOpenMaximal F (V.apartment.specialCompactSubgroup x)) :
    haveI := leviScheme_isAffineHom V.i ξ J
    ∀ v : cocharacterLattice V.S, IsGenericCocharacter (Standard.leviTorusHom V.i ξ J) v →
    let L := V.apartment.specialCompactLeviSubgroup ξ J x
    SpecialCompactProperties F (Standard.leviTorusHom V.i ξ J) v L ∧
      BruhatTits.Iwasawa.ParabolicPointProductFamily (Standard.leviTorusHom V.i ξ J) v L ∧
      ∀ KM : OpenSubgroup (rationalPoints (Standard.leviScheme V.i ξ J)), KM.toSubgroup = L →
        WeakExpansion.IsSpecialVertexCompact v
          (Standard.isMaximalSplitTorus_leviTorusHom V.i ξ J V.isMaximalSplitTorus) KM := by
  let : IsAffineHom (Standard.leviScheme V.i ξ J).X.hom := leviScheme_isAffineHom V.i ξ J
  intro v hv
  obtain ⟨B, rfl⟩ := ParahoricBuildingData.exists_toValuationBuildingData_eq V
  let hM := standardLevi_isConnectedReductive B.isConnectedReductive B.i B.isMaximalSplitTorus ξ hξ J hJ
  have hiM := Standard.isMaximalSplitTorus_leviTorusHom B.i ξ J B.isMaximalSplitTorus
  obtain ⟨BM, hSM, hiBM, hAM, hBound, hMdata⟩ := exists_specialCompactBuildingDataAt hiM hM
  obtain ⟨xM, hxM, heq⟩ := exists_specialCompactLevi_of_buildingGeometry B hA ξ hξ J hJ x hx hK
    BM.i BM.centralizer BM.apartment BM.isOmegaCompatible hAM.topologyCompatible hSM hiBM
    (fun _ _ y hy => (hMdata y hy).1)
  let L := B.apartment.specialCompactLeviSubgroup ξ J x
  have hProduct (w : cocharacterLattice BM.S) (hw : IsGenericCocharacter BM.i w) :
      BruhatTits.Iwasawa.ParabolicPointProductFamily BM.i w L := by
    dsimp only [L]
    rw [← heq]
    exact ((hMdata xM hxM).2 w hw).2.1
  have hSpecial (w : cocharacterLattice BM.S) (hw : IsGenericCocharacter BM.i w) :
      SpecialCompactProperties F BM.i w L := by
    dsimp only [L]
    rw [← heq]
    have hMax := (hMdata xM hxM).1
    have hWeyl := ((hMdata xM hxM).2 w hw).1
    obtain ⟨hLowerMax, _⟩ := specialPacketLeviProperties BM hAM w hw xM hxM hMax
    exact ⟨isBoundedOpenMaximal_of_isCompactOpenMaximal BM.isConnectedReductive hMax, hMax, hWeyl,
      hasParabolicFactorization_of_maximal_compact_levis BM.isConnectedReductive BM.i
        BM.isMaximalSplitTorus w hw _ hMax.1 hLowerMax⟩
  have hVertex (w : cocharacterLattice BM.S) (hw : IsGenericCocharacter BM.i w)
      (KM : OpenSubgroup (rationalPoints (Standard.leviScheme B.i ξ J)))
      (hKM : KM.toSubgroup = L) : WeakExpansion.IsSpecialVertexCompact w BM.isMaximalSplitTorus KM :=
    ⟨BM.centralizer, BM.apartment, hAM, hBound, xM, hxM, heq.symm ▸ hSpecial w hw,
      heq.trans hKM.symm⟩
  refine ⟨specialCompactProperties_of_heq hSM hiBM L hSpecial v hv,
    parabolicPointProductFamily_of_heq hSM hiBM L hProduct v hv, fun KM hKM => ?_⟩
  obtain ⟨w, hw, hwgen⟩ := exists_genericCocharacter_heq hSM hiBM v hv
  exact isSpecialVertexCompact_of_heq hSM hiBM BM.isMaximalSplitTorus hiM hw (hVertex w hwgen KM hKM)

variable [LocallyOfFiniteType G.X.hom]

local instance traceModelAffine (p : SemistandardSpectralIndex i) (m : LeviModel p) :
    IsAffineHom m.scheme.X.hom := m.reductive.isAffineHom

/-- A model of the actual semistandard Levi with the trace of the given
ambient special compact, and its structural properties at the inherited torus. -/
structure SemistandardLeviCompactTrace (p : SemistandardSpectralIndex i)
    (K : OpenSubgroup (rationalPoints G)) (v : cocharacterLattice S) where
  model : LeviModel p
  compact : OpenSubgroup (rationalPoints model.scheme)
  trace : ∀ x : rationalPoints model.scheme, x ∈ compact ↔ rationalPoints.map model.inclusion x ∈ K
  isCompact : IsCompact (compact : Set (rationalPoints model.scheme))
  generic : IsGenericCocharacter (semistandardLeviSplitTorus p model.represents) v
  special : SpecialCompactProperties F (semistandardLeviSplitTorus p model.represents) v compact.toSubgroup
  iwasawa : IsIwasawaPair
    (standardParabolicPoints (semistandardLeviSplitTorus p model.represents) v ∅) compact.toSubgroup

variable {hi}

/-- The compact trace is itself the norm-one fixer of a special vertex
in the apartment of the inherited maximal split torus. -/
def SemistandardLeviCompactTrace.IsSpecialVertex {p : SemistandardSpectralIndex i}
    {K : OpenSubgroup (rationalPoints G)} {v : cocharacterLattice S}
    (s : SemistandardLeviCompactTrace p K v) (hi : IsMaximalSplitTorus i) : Prop :=
  haveI := s.model.reductive.isAffineHom
  WeakExpansion.IsSpecialVertexCompact v
    (isMaximalSplitTorus_semistandardLeviSplitTorus p s.model.represents s.model.closed hi) s.compact

variable (hi)

set_option maxRecDepth 4096 in
set_option maxHeartbeats 2200000 in
/-- The inherited special compact on the actual Levi, together with its
special vertex witness at the inherited maximal split torus. -/
def semistandardLeviCompactTraceWithVertex (hG : IsConnectedReductive G)
    (hν : IsGenericCocharacter i ν)
    (K : OpenSubgroup (rationalPoints G)) (hK : WeakExpansion.IsSpecialVertexCompact ν hi K)
    (p : SemistandardSpectralIndex i) : {s : SemistandardLeviCompactTrace p K ν // s.IsSpecialVertex hi} := by
  apply Classical.choice
  let : Mono i.hom.hom.left := mono_of_isMaximalSplitTorus hi
  obtain ⟨ξ, hξ, J, hJ, hp⟩ := exists_standard_presentation hG hi p
  obtain ⟨C, D, hA, _, x, hx, hspecial, hKx⟩ := hK
  let V : ValuationBuildingData (F := F) G := ⟨hG, S, i, hi, D, C, hA.omegaCompatible⟩
  let m : LeviModel (SemistandardSpectralIndex.ofStandard hG hi ξ hξ J hJ) :=
    ⟨Standard.leviScheme i ξ J, Standard.leviHom i ξ J, Standard.isRepresentedBy_leviHom i ξ J,
      Standard.isClosedSubgroup_leviHom i ξ J, standardLevi_isConnectedReductive hG i hi ξ hξ J hJ⟩
  subst p
  let iL := Standard.leviTorusHom i ξ J
  have heq : semistandardLeviSplitTorus _ m.represents = iL := by
    apply Grp.hom_ext
    have : Mono m.inclusion.hom.hom := m.represents.1
    apply (cancel_mono m.inclusion.hom.hom).mp
    rw [← Grp.comp_hom_hom, ← Grp.comp_hom_hom, semistandardLeviSplitTorus_comp]
    exact congrArg (fun f => f.hom.hom) (Standard.leviTorusHom_comp i ξ J).symm
  let : IsAffineHom (Standard.leviScheme i ξ J).X.hom := m.reductive.isAffineHom
  have hgen : IsGenericCocharacter iL ν := fun α hα => hν α
    (relativeRoots_subset_of_factor m.represents iL (Standard.leviTorusHom_comp i ξ J) hα)
  obtain ⟨hL, hProd, hVertex⟩ := standardLeviTraceProperties V hA ξ hξ J hJ x hx hspecial.2.1 ν hgen
  change SpecialCompactProperties F iL ν (D.specialCompactLeviSubgroup ξ J x) at hL
  let L : OpenSubgroup (rationalPoints m.scheme) := ⟨D.specialCompactLeviSubgroup ξ J x, hL.2.1.2.1⟩
  have hTrace (y : rationalPoints m.scheme) : y ∈ L ↔ rationalPoints.map m.inclusion y ∈ K := by
    change rationalPoints.map (Standard.leviHom i ξ J) y ∈ D.specialCompactSubgroup x ↔
      rationalPoints.map m.inclusion y ∈ K
    rw [hKx]
    rfl
  have hIwasawa : IsIwasawaPair
      (standardParabolicPoints (semistandardLeviSplitTorus _ m.represents) ν ∅) L.toSubgroup := by
    rw [heq]
    exact isIwasawaPair_of_pointProductEqualities (hProd.2.2.1 ∅ (Set.empty_subset _))
  let s : SemistandardLeviCompactTrace _ K ν :=
    ⟨m, L, hTrace, hL.2.1.1, heq ▸ hgen, heq ▸ hL, hIwasawa⟩
  refine ⟨⟨s, ?_⟩⟩
  change WeakExpansion.IsSpecialVertexCompact ν
    (isMaximalSplitTorus_semistandardLeviSplitTorus _ m.represents m.closed hi) L
  exact isSpecialVertexCompact_of_heq rfl heq.symm.heq
    (Standard.isMaximalSplitTorus_leviTorusHom i ξ J hi)
    (isMaximalSplitTorus_semistandardLeviSplitTorus _ m.represents m.closed hi) HEq.rfl
    (hVertex L rfl)

/-- Realize the inherited special compact for each actual semistandard Levi,
with the same ambient compact and the original cocharacter. -/
def semistandardLeviCompactTrace (hG : IsConnectedReductive G) (hν : IsGenericCocharacter i ν)
    (K : OpenSubgroup (rationalPoints G)) (hK : WeakExpansion.IsSpecialVertexCompact ν hi K)
    (p : SemistandardSpectralIndex i) : SemistandardLeviCompactTrace p K ν :=
  Classical.choice ⟨(semistandardLeviCompactTraceWithVertex hi ν hG hν K hK p).val⟩

end SemistandardTrace

end Langlands.HarishChandraSchwartz
