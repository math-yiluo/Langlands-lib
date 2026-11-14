import Langlands.BruhatTits.IntegralModels.OrderedIntegralOpenCell
import Langlands.BruhatTits.IntegralModels.IntegralTorusCentralizer
import Langlands.BruhatTits.IntegralModels.UnramifiedIntegralRoots
import Langlands.BruhatTits.IntegralModels.UnramifiedZeroRoots
import Langlands.BruhatTits.IntegralModels.UnramifiedModelKernelTorus
import Langlands.BruhatTits.IntegralModels.UnramifiedTorusIwahoriModelAssembly
import Langlands.GroupScheme.IntegralModel.SmoothHomExtensionProof
import Langlands.GroupScheme.IntegralModel.SmoothIntersection
import Langlands.Geometry.Building.UnramifiedStabilizerDescent

/-! # Actual torus/root model families inside zero-fixer models -/

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry
open scoped CategoryTheory.MonObj ValuativeRel
open Langlands.GroupScheme Langlands.LocalGalois.Separable
open Langlands.GroupScheme.GaloisPointComparison
open Langlands.Geometry.Building

namespace Langlands.BruhatTits.IntegralModels

namespace OrderedIntegralOpenCell

variable {F : Type u} [Field F] [ValuativeRel F] [TopologicalSpace F]
  [IsNonarchimedeanLocalField F]
  {G : GroupScheme (Spec (CommRingCat.of (inertiaFixedField F)))}
  [IsAffineHom G.X.hom]
  (C : MaximalUnramified.BuildingData F G) (E : UnramifiedZeroDatum F G)
  (Ω : Set C.Apartment)
  (N : IntegralModel (fixedFieldIntegers F) (inertiaFixedField F) G)

local instance : IsDiscreteValuationRing (fixedFieldIntegers F) :=
  fixedFieldIntegersIsDVR_of_valuesFromBase F (fixedFieldValuesFromBase F)

/-- A zero-fixer model contains an actual closed integral split torus with the
prescribed generic apartment torus. -/
theorem exists_integralSplitTorusData
    (hpts : N.integralPoints = E.zeroPoints ⊓ C.pointwiseFixer (C.apartmentMap '' Ω)) :
    ∃ T : IntegralSplitTorusData N C.i, IsClosedSubgroup T.inclusion := by
  let : IsAlgClosed (IsLocalRing.ResidueField (fixedFieldIntegers F)) :=
    (fixedFieldResidueIsAlgClosure F).1
  have hv : ∀ a : (fixedFieldIntegers F)ˣ,
      MaximalUnramified.valuation F
        (algebraMap (fixedFieldIntegers F) (inertiaFixedField F) (a : fixedFieldIntegers F)) = 1 := by
    intro a
    have h := (Valuation.valuationSubring.integers (fixedFieldValuation F)).valuation_unit a
    have h' := ((MaximalUnramified.valuation_isEquiv F).eq_iff).mpr
      (h.trans (map_one (fixedFieldValuation F)).symm)
    simpa only [map_one] using h'
  obtain ⟨T, j, e, hT, hj, hcomm⟩ :=
    IntegralModel.SplitTorusClosure.exists_isSplitTorus_genericTorusMap_eq_of_bounded
      N (MaximalUnramified.valuation F) hv C.i C.isMaximalSplitTorus.isSplitSubtorus.1
      C.isMaximalSplitTorus.isSplitSubtorus.2
      (by rw [hpts]; exact map_characterValuationKernel_le_zeroPoints_inf_pointwiseFixer C E Ω)
  exact ⟨⟨T, hT, j, e, hcomm⟩, hj⟩

variable {C E Ω N} [Smooth N.group.X.hom]

/-- The actual root-filtration model of a relative root inside a zero-fixer model. -/
def rootData (hpts : N.integralPoints = E.zeroPoints ⊓ C.pointwiseFixer (C.apartmentMap '' Ω))
    (hne : Ω.Nonempty) (hb : ∀ f : C.Apartment →ᵃ[ℝ] ℝ, BddAbove (f '' Ω))
    (T : IntegralSplitTorusData N C.i) (x : C.Apartment) (a : relativeRoots C.i) :
    RootFiltrationModelData (fixedFieldIntegers F) (inertiaFixedField F)
      C.apartment x a (C.apartment.rootFixerDepth a x Ω) where
  rootGroup := T.rootGroup a a.2.1
  inclusion := T.rootInclusion a a.2.1
  isRootSubgroup := T.rootInclusion_isRootSubgroup a a.2.1
  model := T.rootModel a a.2.1
  smooth := IntegralModel.SplitRoot.model_isSmooth N T.isSplit T.inclusion
    (T.integralCharacter a) (T.integralCharacter_ne_zero a.2.1)
  geometricallyConnected := IntegralModel.SplitRoot.model_hasGeometricallyConnectedFibres N
    T.isSplit T.inclusion (T.integralCharacter a) (T.integralCharacter_ne_zero a.2.1)
  integralPoints_eq := by
    rw [T.rootModel_integralPoints_eq a a.2.1, hpts, inf_comm,
      rootGroupPoints_inf_unramifiedZeroFixer_eq_rootFixer C E Ω a]
    exact C.apartment.rootFixer_eq_filtration_of_bounded a x hne hb

variable (hrep : (torusCentralizer C.i).IsRepresentedBy E.i)
  [GeometricallyConnected E.T.toGrp.X.hom]

set_option maxHeartbeats 1600000 in
/-- The actual family: root models of the integral split torus and the relative
identity component of its integral centralizer, with their compatible maps. -/
def family (hpts : N.integralPoints = E.zeroPoints ⊓ C.pointwiseFixer (C.apartmentMap '' Ω))
    (hne : Ω.Nonempty) (hb : ∀ f : C.Apartment →ᵃ[ℝ] ℝ, BddAbove (f '' Ω))
    (T : IntegralSplitTorusData N C.i) (x : C.Apartment)
    {H : GroupScheme (Spec (CommRingCat.of (fixedFieldIntegers F)))}
    {iH : H ⟶ (T.centralizerModel E.i hrep).group}
    (hiH : IsRelativeIdentityComponent _ iH) (hH : Smooth H.X.hom)
    (hgc : GeometricallyConnected H.X.hom)
    (htor : ((T.centralizerModel E.i hrep).neutralModel
      (T.centralizerModel_isSmooth E.i hrep) hiH hH).integralPoints = E.torusIwahori) :
    TorusRootModelFamilyData C E x Ω N where
  torusModel := (T.centralizerModel E.i hrep).neutralModel
    (T.centralizerModel_isSmooth E.i hrep) hiH hH
  torusSmooth := hH
  torusGeometricallyConnected := hgc
  torusPoints_eq := htor
  torusMap :=
    { hom := iH ≫ T.centralizerIntegralInclusion
      generic_comm := by
        have hc := (T.centralizerModelMap E.i hrep).generic_comm
        change (GroupScheme.baseChange _).map T.centralizerIntegralInclusion ≫ _ = _ at hc
        change _ = ((T.centralizerModel E.i hrep).neutralGenericIso
          (T.centralizerModel_isSmooth E.i hrep) hiH ≪≫
            (T.centralizerModel E.i hrep).genericIso).hom ≫ E.i
        rw [Iso.trans_hom, IntegralModel.neutralGenericIso_hom, Category.assoc, ← hc,
          Functor.map_comp, Category.assoc] }
  rootModel := rootData hpts hne hb T x
  rootMap := fun a => T.rootModelMap a a.2.1

omit [IsAffineHom G.X.hom] [GeometricallyConnected E.T.toGrp.X.hom] in
set_option maxHeartbeats 800000 in
/-- The torus Iwahori subgroup has unit rational-character values. -/
theorem torusIwahori_le_characterValuationKernel :
    E.torusIwahori ≤
      characterValuationKernel (MaximalUnramified.valuation F) E.T.toGrp := by
  rw [characterValuationKernel_eq_of_isEquiv (MaximalUnramified.valuation_isEquiv F)]
  let : (fixedFieldValuation F).HasExtension (intermediateValuation F E.L) :=
    intermediateValuation_extends_fixedField F E.L
  change torusNormIwahori (UnramifiedClosure F) E.L (intermediateValuation F E.L) E.T ≤ _
  exact torusNormIwahori_le_characterValuationKernel
    (k := UnramifiedClosure F) (L := E.L)
    (LocalGalois.Separable.fixedFieldValuation F) (intermediateValuation F E.L)
    (intermediateValuation_conjugate F E.L) E.T

include hrep in
omit [GeometricallyConnected E.T.toGrp.X.hom] in
/-- Bounded points of the zero datum's torus fix the whole apartment. -/
theorem map_mem_pointwiseFixer_of_mem_characterValuationKernel
    {t : rationalPoints E.T.toGrp}
    (ht : t ∈ characterValuationKernel (MaximalUnramified.valuation F) E.T.toGrp) :
    rationalPoints.map E.i t ∈ C.pointwiseFixer (C.apartmentMap '' Ω) := by
  let e := hrep.isoOfIsRepresentedBy C.centralizer.isRepresentedBy
  have he : e.hom ≫ C.centralizer.j = E.i :=
    hrep.isoOfIsRepresentedBy_hom_comp C.centralizer.isRepresentedBy
  have hz := IntegerValuation.map_mem_characterValuationKernel (MaximalUnramified.valuation F)
    e.hom ht
  have hmap : rationalPoints.map E.i t =
      rationalPoints.map C.centralizer.j (rationalPoints.map e.hom t) := by
    rw [← he]
    rfl
  change rationalPoints.map E.i t ∈ C.apartment.pointwiseFixer _
  rw [KPApartmentData.mem_pointwiseFixer]
  rintro _ ⟨y, -, rfl⟩
  rw [hmap]
  exact (C.mem_oneStabilizer.mp (C.map_mem_oneStabilizer hz y)).2

omit [GeometricallyConnected E.T.toGrp.X.hom] in
/-- The torus Iwahori image lies in the integral centralizer. -/
theorem torusIwahori_le_centralizerModel
    (hpts : N.integralPoints = E.zeroPoints ⊓ C.pointwiseFixer (C.apartmentMap '' Ω))
    (T : IntegralSplitTorusData N C.i) :
    E.torusIwahori ≤ (T.centralizerModel E.i hrep).integralPoints := by
  rw [T.centralizerModel_integralPoints_eq_comap E.i hrep, hpts]
  intro t ht
  rw [Subgroup.mem_comap, Subgroup.mem_inf]
  exact ⟨E.map_torusIwahori_le_zeroPoints (Subgroup.mem_map_of_mem _ ht),
    map_mem_pointwiseFixer_of_mem_characterValuationKernel hrep
      (torusIwahori_le_characterValuationKernel ht)⟩

set_option maxHeartbeats 1600000 in
/-- Under the two torus inputs, the relative identity component of the integral
centralizer has integral points exactly the torus Iwahori subgroup. -/
theorem neutralCentralizer_integralPoints_eq
    (hConn : UnramifiedTorusConnectedBoundStatement.{u})
    (hImg : UnramifiedTorusIwahoriConnectedImageStatement.{u})
    (hpts : N.integralPoints = E.zeroPoints ⊓ C.pointwiseFixer (C.apartmentMap '' Ω))
    (T : IntegralSplitTorusData N C.i)
    {H : GroupScheme (Spec (CommRingCat.of (fixedFieldIntegers F)))}
    {iH : H ⟶ (T.centralizerModel E.i hrep).group}
    (hiH : IsRelativeIdentityComponent _ iH) (hH : Smooth H.X.hom)
    (hgc : GeometricallyConnected H.X.hom) :
    ((T.centralizerModel E.i hrep).neutralModel
      (T.centralizerModel_isSmooth E.i hrep) hiH hH).integralPoints = E.torusIwahori := by
  apply le_antisymm
  · change _ ≤ torusNormIwahori (UnramifiedClosure F) E.L (intermediateValuation F E.L) E.T
    exact hConn F E.T E.L E.isSplitTorus _ hH hgc
  · obtain ⟨S', W, n, hW, hWgc, hWpts⟩ := hImg F E.T E.L E.isSplitTorus
    obtain ⟨φ⟩ := exists_hom_of_map_integralPoints_le IntegralModel.smoothHomExtension F hW
      hWpts (torusIwahori_le_centralizerModel hrep hpts T)
    have : GeometricallyConnected W.group.X.hom := hWgc
    obtain ⟨y, hy⟩ := hiH.exists_hom_lift φ.hom
    change torusNormIwahori (UnramifiedClosure F) E.L (intermediateValuation F E.L) E.T ≤ _
    rw [← hWpts]
    exact map_integralPoints_le_neutralModel _ _ hiH hH φ hy

end OrderedIntegralOpenCell

end Langlands.BruhatTits.IntegralModels
