import Langlands.BruhatTits.IntegralModels.UnramifiedNeutralGeneration
import Langlands.BruhatTits.IntegralModels.UnramifiedTorusIwahoriModelAssembly
import Langlands.GroupScheme.IntegralModel.SmoothHomExtensionProof

/-! # The torus Iwahori contribution to unramified neutral integral points -/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry
open scoped CategoryTheory.MonObj
open Langlands.GroupScheme Langlands.Geometry.Building
open Langlands.LocalGalois.Separable

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

namespace Langlands.BruhatTits.IntegralModels

variable {F : Type u} [Field F] [ValuativeRel F] [TopologicalSpace F]
    [IsNonarchimedeanLocalField F]
    {G : GroupScheme (Spec (CommRingCat.of (inertiaFixedField F)))}
    [IsAffineHom G.X.hom]
    (C : MaximalUnramified.BuildingData F G)
    (E : UnramifiedZeroDatum F G)
    (hE : (torusCentralizer C.i).IsRepresentedBy E.i)
    (Ω : Set C.Apartment)

include hE in
/-- Character-unit points of a torus representing the actual apartment
centralizer lie in the full one-fixer of every apartment subset. -/
theorem map_compatibleTorus_characterValuationKernel_le_oneFixer :
    (characterValuationKernel (MaximalUnramified.valuation F) E.T.toGrp).map
        (rationalPoints.map E.i) ≤
      characterValuationKernel (MaximalUnramified.valuation F) G ⊓
        C.pointwiseFixer (C.apartmentMap '' Ω) := by
  rintro _ ⟨t, ht, rfl⟩
  refine ⟨map_characterValuationKernel_le _ E.i ⟨t, ht, rfl⟩, ?_⟩
  let e := hE.isoOfIsRepresentedBy C.centralizer.isRepresentedBy
  have he : e.hom ≫ C.centralizer.j = E.i :=
    hE.isoOfIsRepresentedBy_hom_comp C.centralizer.isRepresentedBy
  have hz : rationalPoints.map e.hom t ∈
      characterValuationKernel (MaximalUnramified.valuation F) C.centralizer.Z :=
    map_characterValuationKernel_le _ e.hom ⟨t, ht, rfl⟩
  have hp : rationalPoints.map C.centralizer.j (rationalPoints.map e.hom t) =
      rationalPoints.map E.i t := by
    simpa only [rationalPoints.map_apply, Grp.comp_hom_hom, Category.assoc] using
      congrArg (fun f : E.T.toGrp ⟶ G => t ≫ f.hom.hom) he
  apply C.apartment.mem_pointwiseFixer.mpr
  rintro _ ⟨x, _, rfl⟩
  rw [← hp]
  exact (C.mem_oneStabilizer.1 (C.map_mem_oneStabilizer hz x)).2

omit [IsAffineHom G.X.hom] in
/-- The norm-defined Iwahori subgroup has character-unit values for the
normalized integer valuation on the actual maximal unramified field. -/
theorem compatibleTorusIwahori_le_characterValuationKernel :
    E.torusIwahori ≤
      characterValuationKernel (MaximalUnramified.valuation F) E.T.toGrp := by
  intro t ht
  have hfixed := torusNormIwahori_le_characterValuationKernel
    (fixedFieldValuation F) (intermediateValuation F E.L)
    (intermediateValuation_conjugate F E.L) E.T ht
  rw [mem_characterValuationKernel] at hfixed ⊢
  intro χ
  exact (MaximalUnramified.valuation_isEquiv F).eq_one_iff_eq_one.mpr (hfixed χ)

include hE in
/-- The specified torus Iwahori points lie in the full one-fixer of every
apartment subset, through their original generic inclusion. -/
theorem map_compatibleTorusIwahori_le_oneFixer :
    E.torusIwahori.map (rationalPoints.map E.i) ≤
      characterValuationKernel (MaximalUnramified.valuation F) G ⊓
        C.pointwiseFixer (C.apartmentMap '' Ω) :=
  (Subgroup.map_mono (compatibleTorusIwahori_le_characterValuationKernel E)).trans
    (map_compatibleTorus_characterValuationKernel_le_oneFixer C E hE Ω)

variable (D : RelativeComponentModelData (fixedFieldIntegers F) (inertiaFixedField F) G)
    (hN : D.full.integralPoints =
      characterValuationKernel (MaximalUnramified.valuation F) G ⊓
        C.pointwiseFixer (C.apartmentMap '' Ω))

private instance : Smooth D.neutral.group.X.hom := D.neutral_smooth

/-- The actual smooth integral centralizer inside the neutral model, with
generic group the specified maximal torus and generic inclusion exactly `E.i`. -/
def compatibleNeutralCentralizerModel :
    IntegralModel (fixedFieldIntegers F) (inertiaFixedField F) E.T.toGrp :=
  (unramifiedNeutralSplitTorusData C D Ω hN).centralizerModel E.i hE

set_option maxHeartbeats 800000 in
include hE hN in
/-- A connected smooth model of the torus Iwahori subgroup maps into the
neutral component of any supplied full one-fixer model. -/
theorem map_compatibleTorusIwahori_le_neutral
    (hModel : UnramifiedTorusIwahoriModelStatement.{u}) :
    E.torusIwahori.map (rationalPoints.map E.i) ≤ D.neutral.integralPoints := by
  obtain ⟨W, hW, hWgc, hWpts⟩ := hModel F E.T E.L E.isSplitTorus
  change W.integralPoints = E.torusIwahori at hWpts
  have hle : W.integralPoints.map (rationalPoints.map E.i) ≤ D.full.integralPoints := by
    rw [hWpts, hN]
    exact map_compatibleTorusIwahori_le_oneFixer C E hE Ω
  obtain ⟨φ⟩ := exists_hom_of_map_integralPoints_le
    IntegralModel.smoothHomExtension F hW rfl hle
  let : GeometricallyConnected W.group.X.hom := hWgc
  rw [← hWpts]
  rintro _ ⟨t, ht, rfl⟩
  exact (D.factorConnectedModelHom φ).map_mem_integralPoints ht

set_option maxHeartbeats 800000 in
/-- Given the connected torus-model existence and bound statements, the
constructed neutral centralizer realizes exactly the torus Iwahori subgroup. -/
theorem compatibleNeutralCentralizerModel_integralPoints_eq
    (hModel : UnramifiedTorusIwahoriModelStatement.{u})
    (hBound : UnramifiedTorusConnectedBoundStatement.{u}) :
    (compatibleNeutralCentralizerModel C E hE Ω D hN).integralPoints = E.torusIwahori := by
  let A : IntegralSplitTorusData D.neutral C.i :=
    unramifiedNeutralSplitTorusData C D Ω hN
  change (A.centralizerModel E.i hE).integralPoints = E.torusIwahori
  obtain ⟨H, j, hj, _, hH⟩ :=
    RelativeIdentityComponent.smoothExistence _ D.full.group D.full_smooth
  let : GeometricallyConnected H.X.hom := hH
  let : GeometricallyConnected D.neutral.group.X.hom :=
    D.isRelativeComponent.geometricallyConnected hj
  apply le_antisymm
  · exact hBound F E.T E.L E.isSplitTorus _
      (A.centralizerModel_isSmooth E.i hE)
      (A.centralizerModel_hasGeometricallyConnectedFibres E.i hE)
  · rw [A.centralizerModel_integralPoints_eq_comap E.i hE]
    intro t ht
    exact map_compatibleTorusIwahori_le_neutral C E hE Ω D hN hModel
      ⟨t, ht, rfl⟩

set_option maxHeartbeats 800000 in
include hE hN in
/-- Given those two torus statements, the torus Iwahori contribution and the
actual apartment root fixers generate all neutral integral points. -/
theorem compatibleTorusIwahori_sup_sharpFixer_eq_neutral
    (hModel : UnramifiedTorusIwahoriModelStatement.{u})
    (hBound : UnramifiedTorusConnectedBoundStatement.{u}) :
    E.torusIwahori.map (rationalPoints.map E.i) ⊔ C.sharpFixer Ω =
      D.neutral.integralPoints := by
  let A : IntegralSplitTorusData D.neutral C.i :=
    unramifiedNeutralSplitTorusData C D Ω hN
  have hT := compatibleNeutralCentralizerModel_integralPoints_eq C E hE Ω D hN hModel hBound
  change (A.centralizerModel E.i hE).integralPoints = E.torusIwahori at hT
  rw [← hT, A.centralizerModel_map_integralPoints_eq E.i hE]
  have hgen := unramifiedNeutralRootCentralizerGroup_eq_neutral C D Ω hN
  change (A.centralizerModel C.centralizer.j C.centralizer.isRepresentedBy).integralPoints.map
      (rationalPoints.map C.centralizer.j) ⊔ C.sharpFixer Ω = _ at hgen
  rw [A.centralizerModel_map_integralPoints_eq C.centralizer.j
    C.centralizer.isRepresentedBy] at hgen
  exact hgen

/-- The resulting equivalence retains every point's original ambient value. -/
def compatibleTorusIwahoriSharpFixerEquiv
    (hModel : UnramifiedTorusIwahoriModelStatement.{u})
    (hBound : UnramifiedTorusConnectedBoundStatement.{u}) :
    ↥(E.torusIwahori.map (rationalPoints.map E.i) ⊔ C.sharpFixer Ω) ≃*
      D.neutral.integralPoints :=
  MulEquiv.subgroupCongr
    (compatibleTorusIwahori_sup_sharpFixer_eq_neutral C E hE Ω D hN hModel hBound)

@[simp]
theorem coe_compatibleTorusIwahoriSharpFixerEquiv
    (hModel : UnramifiedTorusIwahoriModelStatement.{u})
    (hBound : UnramifiedTorusConnectedBoundStatement.{u})
    (t : ↥(E.torusIwahori.map (rationalPoints.map E.i) ⊔ C.sharpFixer Ω)) :
    (compatibleTorusIwahoriSharpFixerEquiv C E hE Ω D hN hModel hBound t :
      rationalPoints G) = t := rfl

end Langlands.BruhatTits.IntegralModels
