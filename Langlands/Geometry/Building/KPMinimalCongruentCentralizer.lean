import Langlands.Geometry.Building.KPMinimalCongruentMoyPrasadGroups
import Langlands.Geometry.Building.KPMoyPrasadFiltration
import Langlands.Geometry.Building.KPUnramifiedComparisonZeroFieldProof
import Langlands.Geometry.Building.RootFreeApartmentConstruction
import Langlands.Geometry.Building.RootFreeBuildingGeometry
import Langlands.Geometry.Building.SpecialTorusExistenceProof
import Langlands.Geometry.Building.UnramifiedValuationDescentProof
import Langlands.GroupScheme.Dynamic.CentralizerReductiveProof
import Langlands.GroupScheme.Rational.CentralRootRestriction

/-! # The centralizer point groups of KP §9.8 -/

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 1600000

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry
open scoped CategoryTheory.MonObj NNReal
open Langlands.GroupScheme Langlands.GroupScheme.GaloisPointComparison

namespace Langlands.Geometry.Building.ParahoricBuildingData

variable {F : Type u} [Field F] [ValuativeRel F] [TopologicalSpace F]
  [IsNonarchimedeanLocalField F]
  {G : GroupScheme (Spec (CommRingCat.of F))} [IsAffineHom G.X.hom]
  (P : ParahoricBuildingData G)

local notation "K" => UnramifiedClosure F
local notation "ZGroup" => P.centralizer.Z

private theorem centralizerConnectedReductive : IsConnectedReductive ZGroup :=
  P.isMaximalSplitTorus.isSplitSubtorus.1.isConnectedReductive_centralizer_of_dynamic
    dynamicCentralizerReductive P.isConnectedReductive P.i P.centralizer.j
    P.centralizer.isRepresentedBy P.centralizer.isClosedSubgroup

theorem centralizerAffineHom : IsAffineHom (ZGroup).X.hom :=
  P.centralizerConnectedReductive.isAffineHom

attribute [local instance] centralizerAffineHom

private theorem centralizerFactor_eq :
    torusCentralizerFactor P.i P.centralizer.isRepresentedBy = P.centralizer.s := by
  let : Mono P.centralizer.j.hom.hom := P.centralizer.isRepresentedBy.1
  let : Mono P.centralizer.j := (Grp.forget _).mono_of_mono_map
    (inferInstanceAs (Mono P.centralizer.j.hom.hom))
  apply (cancel_mono P.centralizer.j).mp
  rw [torusCentralizerFactor_comp, P.centralizer.comp_eq]

private theorem centralizerFactor_isCentral : IsCentral P.centralizer.s := by
  rw [← P.centralizerFactor_eq]
  exact isCentral_torusCentralizerFactor P.i P.centralizer.isRepresentedBy

private theorem centralizerFactor_isMaximalSplitTorus :
    IsMaximalSplitTorus P.centralizer.s := by
  rw [← P.centralizerFactor_eq]
  exact P.isMaximalSplitTorus.isMaximalSplitTorus_torusCentralizerFactor
    P.centralizer.isRepresentedBy P.centralizer.isClosedSubgroup

private theorem centralizerFactor_relativeRoots :
    relativeRoots P.centralizer.s = ∅ := by
  have : Smooth (ZGroup).X.hom := P.centralizerConnectedReductive.smooth
  apply Set.eq_empty_iff_forall_notMem.mpr
  intro a ha
  have h := root_restrict_eq_zero_of_isCentral P.centralizer.s (𝟙 P.S)
    P.centralizerFactor_isMaximalSplitTorus.isSplitSubtorus.1
    (by
      change IsCentral (𝟙 P.S.toGrp ≫ P.centralizer.s)
      rw [Category.id_comp]
      exact P.centralizerFactor_isCentral) ha
  exact (mem_relativeRoots.mp ha).1 ((Category.id_comp a).symm.trans h)

private def centralizerValuationBuilding : ValuationBuildingData ZGroup :=
  ValuationBuildingData.ofRelativeRootsEqEmpty P.centralizerConnectedReductive
    P.centralizer.s P.centralizerFactor_isMaximalSplitTorus P.centralizerFactor_relativeRoots
    { Z := ZGroup
      j := 𝟙 ZGroup
      s := P.centralizer.s
      isClosedSubgroup := IsClosedSubgroup.of_iso (Iso.refl ZGroup)
      isRepresentedBy :=
        ((isCentral_iff_torusCentralizer_eq_top P.centralizer.s).mp
          P.centralizerFactor_isCentral).symm ▸ SubgroupFunctor.top_isRepresentedBy_id ZGroup
      comp_eq := Category.comp_id _
      bijective := P.centralizer.bijective }

/-- Building data of `Z = Z_G(S)`, on the maximal split torus `S` of `Z`.
This apartment has no relative roots, since `S` is central in `Z`. -/
def centralizerParahoricBuilding : ParahoricBuildingData ZGroup := by
  let h := simplyConnectedDerivedCoverExistence F ZGroup P.centralizerConnectedReductive
  exact
    { toValuationBuildingData := P.centralizerValuationBuilding
      zeroDatum :=
        { isMaximalSplitTorus := P.centralizerFactor_isMaximalSplitTorus
          isRepresentedBy := P.centralizerValuationBuilding.centralizer.isRepresentedBy
          centralizerDatum := P.zeroDatum.centralizerDatum
          D := h.choose
          C := h.choose_spec.choose
          d := h.choose_spec.choose_spec.choose
          π := h.choose_spec.choose_spec.choose_spec.choose
          isSimplyConnectedDerivedCover := h.choose_spec.choose_spec.choose_spec.choose_spec } }

local notation "PZ" => P.centralizerParahoricBuilding

theorem centralizerParahoricBuilding_satisfiesApartmentAxioms :
    (PZ).SatisfiesApartmentAxioms :=
  (PZ).apartment.satisfiesApartmentAxioms_of_relativeRoots_eq_empty (PZ).centralizer
    P.centralizerFactor_relativeRoots

/-- A representative in the apartment of the unique point of the reduced building of `Z`. -/
def centralizerBuildingPoint : (PZ).Apartment :=
  ⟨RootFunctionFamily.constantTop, Set.mem_singleton _⟩

theorem centralizerReducedBuilding_eq (y : (PZ).ReducedBuilding) :
    y = (PZ).apartmentMap P.centralizerBuildingPoint := by
  have := (PZ).apartment.subsingleton_apartment_of_relativeRoots_eq_empty
    P.centralizerFactor_relativeRoots
  have hnormalizer : normalizerPoints (PZ).i = ⊤ := by
    apply top_unique
    have hcentralizer : centralizerPoints (PZ).i = ⊤ := by
      change centralizerPoints P.centralizer.s = ⊤
      rw [← torusCentralizer_carrier_base,
        (isCentral_iff_torusCentralizer_eq_top _).mp P.centralizerFactor_isCentral]
      rfl
    rw [← hcentralizer]
    exact centralizerPoints_le_normalizerPoints _
  obtain ⟨z, x, rfl⟩ := (PZ).exists_smul_apartmentMap y
  rw [Subsingleton.elim x P.centralizerBuildingPoint]
  apply (PZ).apartment.mem_reducedFixer.mp
  rw [(PZ).apartment.reducedFixer_apartmentMap_of_relativeRoots_eq_empty
    P.centralizerFactor_relativeRoots, hnormalizer]
  exact Subgroup.mem_top z

/-- A special-torus lift for the centralizer building, chosen using unramified valuation descent. -/
def centralizerUnramifiedApartmentLift :
    Σ t : (PZ).UnramifiedComparisonTorus, t.ApartmentLift :=
  Classical.choice <| by
    obtain ⟨t, ⟨L⟩⟩ := exists_unramifiedApartmentLift
      specialTorusExistence unramifiedValuationDescent PZ
    exact ⟨⟨t, L⟩⟩

/-- The intersection `Z(K)_{x,r} ∩ Z(F)` computed using a special-torus lift of
the unique point of the reduced building of `Z`. -/
def minimalCongruentCentralizerPointsOfLift {t : (PZ).UnramifiedComparisonTorus}
    (L : t.ApartmentLift) (r : ℝ≥0) : Subgroup (rationalPoints ZGroup) :=
  (L.buildingData.minimalCongruentMoyPrasad L.centralizer_isTorus
    (L.e P.centralizerBuildingPoint) r).comap (rationalExtend F K ZGroup)

/-- The family `Z(F)_r` in KP §9.8 for the minimal congruent torus filtration. -/
def minimalCongruentCentralizerPoints (r : ℝ≥0) : Subgroup (rationalPoints ZGroup) :=
  P.minimalCongruentCentralizerPointsOfLift P.centralizerUnramifiedApartmentLift.2 r

/-- At depth zero the construction gives the original `Z(F)^0`, for every special-torus lift. -/
theorem minimalCongruentCentralizerPointsOfLift_zero {t : (PZ).UnramifiedComparisonTorus}
    (L : t.ApartmentLift) :
    P.minimalCongruentCentralizerPointsOfLift L 0 = P.centralizerZero := by
  rw [minimalCongruentCentralizerPointsOfLift,
    L.buildingData.minimalCongruentMoyPrasad_zero]
  have h := unramifiedComparisonZeroField F ZGroup PZ
    P.centralizerParahoricBuilding_satisfiesApartmentAxioms t L P.centralizerBuildingPoint
  have hj : (PZ).centralizer.j = 𝟙 ZGroup := rfl
  change ((L.buildingData.moyPrasad L.centralizer_isTorus
      (L.e P.centralizerBuildingPoint) 0).comap (rationalExtend F K ZGroup)).comap
    (rationalPoints.map (PZ).centralizer.j) = P.centralizerZero at h
  have hid : rationalPoints.map (𝟙 ZGroup) = MonoidHom.id _ := by
    ext z : 1
    simp only [rationalPoints.map_apply, Grp.id_hom_hom, Category.comp_id, MonoidHom.id_apply]
  rw [hj] at h
  change ((L.buildingData.moyPrasad L.centralizer_isTorus
      (L.e P.centralizerBuildingPoint) 0).comap (rationalExtend F K ZGroup)).comap
    (rationalPoints.map (𝟙 ZGroup)) = P.centralizerZero at h
  simpa only [hid, Subgroup.comap_id] using h

theorem minimalCongruentCentralizerPoints_zero :
    P.minimalCongruentCentralizerPoints 0 = P.centralizerZero :=
  P.minimalCongruentCentralizerPointsOfLift_zero P.centralizerUnramifiedApartmentLift.2

/-- The order properties of the constructed family required by `CentralizerFiltration`. -/
def MinimalCongruentCentralizerOrder : Prop :=
  Antitone P.minimalCongruentCentralizerPoints ∧
    (⨅ r : ℝ≥0, P.minimalCongruentCentralizerPoints r) = ⊥

/-- Package the constructed point groups as a `CentralizerFiltration`. -/
def minimalCongruentCentralizerFiltration (h : P.MinimalCongruentCentralizerOrder) :
    P.CentralizerFiltration where
  filtration := P.minimalCongruentCentralizerPoints
  filtration_zero := P.minimalCongruentCentralizerPoints_zero
  antitone := h.1
  separated := h.2

/-- `P_{x,r}` of KP Definition 13.2.1 for the minimal congruent filtration. -/
def minimalCongruentMoyPrasad (h : P.MinimalCongruentCentralizerOrder)
    (x : P.Apartment) (r : ℝ≥0) : Subgroup (rationalPoints G) :=
  (P.minimalCongruentCentralizerFiltration h).moyPrasad x r

/-- `P_{x,r+}` for the minimal congruent filtration, with the strict-depth convention of KP §1.6. -/
def minimalCongruentMoyPrasadPlus (h : P.MinimalCongruentCentralizerOrder)
    (x : P.Apartment) (r : ℝ≥0) : Subgroup (rationalPoints G) :=
  (P.minimalCongruentCentralizerFiltration h).moyPrasadPlus x r

end Langlands.Geometry.Building.ParahoricBuildingData
