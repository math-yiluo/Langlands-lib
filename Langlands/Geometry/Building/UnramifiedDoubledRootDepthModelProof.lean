import Langlands.Geometry.Building.UnramifiedDoubledRootDepthModelStatement
import Langlands.Geometry.Building.UnramifiedRootTranslationPositivity
import Langlands.Geometry.Building.TorusRestrictedRootFixer
import Langlands.Geometry.Building.RootCharacterValuationKernel
import Langlands.Geometry.Building.KPUnramifiedComparisonRootHelpers
import Langlands.BruhatTits.IntegralModels.UnramifiedFixedSubsetModels
import Langlands.BruhatTits.IntegralModels.UnramifiedRecoveredTorusClause
import Langlands.BruhatTits.IntegralModels.IntegralRootRepresentativeModel
import Langlands.BruhatTits.IntegralModels.IntegralTorusFullRootData
import Langlands.GroupScheme.IntegralModel.ClosedUnramifiedPoints
import Langlands.GroupScheme.Rational.RootSubgroupBaseChange

/-! # Smooth doubled-root depth models for supplied apartment lifts -/

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 4000000

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry
open scoped CategoryTheory.MonObj ValuativeRel NNReal
open Langlands.GroupScheme Langlands.GroupScheme.RealTorusSpace
open Langlands.GroupScheme.GaloisPointComparison
open Langlands.LocalGalois.Separable Langlands.BruhatTits.IntegralModels

namespace Langlands.Geometry.Building

private instance doubledRootDepthProofAffineHom {F : Type u} [Field F]
    [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F]
    {G : GroupScheme (Spec (CommRingCat.of F))} [IsAffineHom G.X.hom] :
    IsAffineHom (baseChanged F (UnramifiedClosure F) G).X.hom := by
  change IsAffineHom
    (CategoryTheory.Limits.pullback.snd G.X.hom (baseMap F (UnramifiedClosure F)))
  infer_instance

private theorem rootRepresentative_map_mem
    {k : Type u} [Field k] {S : CommGroupScheme (Spec (CommRingCat.of k))}
    {G U : GroupScheme (Spec (CommRingCat.of k))}
    (i : S.toGrp ⟶ G) (a : characterLattice S) (q : U ⟶ G)
    (hq : (RelativeRoot.subgroup i a).IsRepresentedBy q)
    (x : rationalPoints U) :
    rationalPoints.map q x ∈ rootGroupPoints i a := by
  change rationalPoints.map q x ∈
    (RelativeRoot.subgroup i a).carrier (Over.mk (𝟙 _))
  rw [← hq.2]
  exact ⟨x, rfl⟩

namespace ParahoricBuildingData.UnramifiedComparisonTorus.ApartmentLift

variable {F : Type u} [Field F] [ValuativeRel F] [TopologicalSpace F]
    [IsNonarchimedeanLocalField F]
    {G : GroupScheme (Spec (CommRingCat.of F))} [IsAffineHom G.X.hom]
    {P : ParahoricBuildingData G} {t : P.UnramifiedComparisonTorus}
    (L : t.ApartmentLift)

local notation "b" => algebraBaseMap F (UnramifiedClosure F)
local notation "fK" => CategoryTheory.Functor.map (CommGroupScheme.baseChange b) t.f
local notation "aK" a => characterLattice.baseChange b P.S a

/-- A descended translation with lower evaluation `-r` converts depth zero
at the translated point to depth `r` at the original point. -/
theorem restrictedDepth_descentTranslate
    (z : L.apartment.Apartment) (a : characterLattice P.S)
    (r : ℝ) (v : V P.S) (hv : eval P.S a v = -r) :
    torusRestrictedRootDepthSubgroup
        (L.apartment.descentTranslate t.f P.isMaximalSplitTorus.isSplitSubtorus.1 z v).isValuation
        fK (aK a) 0 =
      torusRestrictedRootDepthSubgroup z.isValuation fK (aK a) r := by
  unfold torusRestrictedRootDepthSubgroup
  refine iSup_congr fun χ => iSup_congr fun hχ => iSup_congr fun m =>
    iSup_congr fun hm => iSup_congr fun heq => ?_
  apply SetLike.coe_injective
  change rootFiltration t.upstairsInclusion
    (descentCocharacterMap F (UnramifiedClosure F) t.f
      P.isMaximalSplitTorus.isSplitSubtorus.1 v +ᵥ z.val) χ (m * 0) =
    rootFiltration t.upstairsInclusion z.val χ (m * r)
  rw [rootFiltration_vadd', eval_descentCocharacterMap, heq,
    eval_nsmul_char, eval_splitCocharacterBaseChange, hv]
  congr 1
  ring

end ParahoricBuildingData.UnramifiedComparisonTorus.ApartmentLift

/-- Every supplied doubled-root representative has the exact smooth connected
depth model on all points over the maximal unramified extension. -/
theorem unramifiedDoubledRootDepthModel :
    UnramifiedDoubledRootDepthModelStatement.{u} := by
  intro F _ _ _ _ G _ P _ t L y a h2a U q hq _ s
  let : Smooth G.X.hom := P.isConnectedReductive.smooth
  let hS := P.isMaximalSplitTorus.isSplitSubtorus.1
  have ha : (2 : ℕ) • a.val ≠ 0 := h2a.1
  obtain ⟨w, hw⟩ := exists_eval_ne_zero hS ha
  let v : V P.S := (-(s : ℝ) / eval P.S (2 • a.val) w) • w
  have hv : eval P.S (2 • a.val) v = -(s : ℝ) := by
    change eval P.S (2 • a.val)
      ((-(s : ℝ) / eval P.S (2 • a.val) w) • w) = _
    rw [map_smul]
    change (-(s : ℝ) / eval P.S (2 • a.val) w) *
      eval P.S (2 • a.val) w = _
    exact div_mul_cancel₀ _ hw
  let z := L.apartment.descentTranslate t.f hS (L.e y) v
  have hz (σ : UnramifiedClosure F ≃ₐ[F] UnramifiedClosure F) :
      RootFunctionFamily.galoisAction F (UnramifiedClosure F) t.T G σ z.val = z.val :=
    L.apartment.galois_fixed_descentTranslate t.f hS (L.e y) (L.fixed y) v σ
  let B := recoveredFixedPointModels L.apartment P.isConnectedReductive
    t.isMaximalSplitTorus L.centralizer L.isOmegaCompatible z hz
  let A := B.lowerApartmentTorus L.centralizer L.isOmegaCompatible
    P.isMaximalSplitTorus t.factor
  let AFull := A.toFullIntegralSplitTorusData
    (B.lowerApartmentTorus_isClosedSplit L.centralizer L.isOmegaCompatible
      P.isMaximalSplitTorus t.factor).1
  let : Smooth B.lower.full.group.X.hom := B.lower.full_smooth
  obtain ⟨M, hM, hMc, φ, hφ⟩ :=
    AFull.exists_model_of_rootRepresentative (2 • a.val) ha U q hq
  refine ⟨M, hM, M.hasConnectedSpecialFibre_of_geometricallyConnected
    (M.hasGeometricallyConnectedSpecialFibre_of_geometricallyConnected hMc), ?_⟩
  intro x
  let b := algebraBaseMap F (UnramifiedClosure F)
  let fK := (CommGroupScheme.baseChange b).map t.f
  let aK := characterLattice.baseChange b P.S (2 • a.val)
  let g := rationalPoints.map ((GroupScheme.baseChange b).map q) x
  have haK : aK ≠ 0 :=
    ((mem_roots_baseChange_iff (K := UnramifiedClosure F) G P.S hS P.i
      (2 • a.val)).mpr h2a).1
  have hqK :
      (RelativeRoot.subgroup
        ((GroupScheme.baseChange b).map P.i) aK).IsRepresentedBy
          ((GroupScheme.baseChange b).map q) := by
    rw [RelativeRoot.subgroup_baseChange]
    exact hq.baseChange b
  have hroot : g ∈ rootGroupPoints (CommGroupScheme.groupHom fK ≫
      t.upstairsInclusion) aK := by
    have hfactor : CommGroupScheme.groupHom fK ≫ t.upstairsInclusion =
        (GroupScheme.baseChange b).map P.i :=
      ParahoricBuildingData.UnramifiedComparisonTorus.ApartmentLift.fieldFactorization
        (t := t)
    rw [hfactor]
    exact rootRepresentative_map_mem (k := UnramifiedClosure F)
        (S := (CommGroupScheme.baseChange b).obj P.S)
        (G := (GroupScheme.baseChange b).obj G)
        (U := (GroupScheme.baseChange b).obj U)
        ((GroupScheme.baseChange b).map P.i) aK
        ((GroupScheme.baseChange b).map q) hqK x
  have hkernel : g ∈ characterValuationKernel (MaximalUnramified.valuation F)
      (baseChanged F (UnramifiedClosure F) G) :=
    rootGroupPoints_le_characterValuationKernel (hS.baseChange b)
      (CommGroupScheme.groupHom fK ≫ t.upstairsInclusion) aK haK
      (MaximalUnramified.valuation F) hroot
  have hdepth := L.apartment.restrictedRootGroupPoints_inf_reducedFixer_eq_depthZero
    L.buildingData.isConnectedReductive t.isMaximalSplitTorus (hS.baseChange b)
    L.oppositeFactorPairs fK aK haK z
  rw [IntegralModel.hasIntegralCoordinates_iff_map_mem_baseChangeUnramified φ hφ x,
    B.recovery.full_integralPoints_eq, B.full_integralPoints,
    Set.image_singleton, L.apartment.pointwiseFixer_singleton]
  change g ∈ _ ⊓ _ ↔ _
  rw [Subgroup.mem_inf, and_iff_right hkernel]
  rw [← L.restrictedDepth_descentTranslate (L.e y) (2 • a.val) s v hv,
    ← hdepth, Subgroup.mem_inf, and_iff_right hroot]

end Langlands.Geometry.Building
