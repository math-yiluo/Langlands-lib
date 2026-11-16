import Langlands.BruhatTits.IntegralModels.IntegralRadicalRootCentralizerGeneration
import Langlands.BruhatTits.IntegralModels.UnramifiedRootPositiveReductionProof
import Langlands.BruhatTits.IntegralModels.UnramifiedZeroFixerConnected
import Langlands.BruhatTits.IntegralModels.ReductiveQuotientExistence

/-! # Radical root intersections of singleton unramified zero fixers -/

noncomputable section

universe u

open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory AlgebraicGeometry
open scoped CategoryTheory.MonObj
open Langlands.GroupScheme Langlands.Geometry.Building
open Langlands.LocalGalois.Separable

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true
set_option maxHeartbeats 1600000

namespace Langlands.BruhatTits.IntegralModels

private theorem geometricallyConnected_of_connectedFibres
    {R K : Type u} [CommRing R] [IsDomain R] [Field K]
    [Algebra R K] [IsFractionRing R K]
    {G : GroupScheme (Spec (CommRingCat.of K))}
    (N : IntegralModel R K G) [Smooth N.group.X.hom]
    (h : N.HasConnectedFibres) : GeometricallyConnected N.group.X.hom := by
  apply (GeometricallyConnected.iff_geometricallyConnected_fiber _).mpr
  intro s
  let H := RelativeIdentityComponent.residueFiber N.group s
  let : ConnectedSpace H.X.left := h s
  let : Smooth H.X.hom :=
    inferInstanceAs (Smooth (pullback.snd N.group.X.hom
      ((Spec (CommRingCat.of R)).fromSpecResidueField s)))
  let : IsAffineHom H.X.hom :=
    inferInstanceAs (IsAffineHom (pullback.snd N.group.X.hom
      ((Spec (CommRingCat.of R)).fromSpecResidueField s)))
  exact H.geometricallyConnected_of_connected

private def selfRelativeComponent
    {R K : Type u} [CommRing R] [IsDomain R] [Field K]
    [Algebra R K] [IsFractionRing R K]
    {G : GroupScheme (Spec (CommRingCat.of K))}
    (N : IntegralModel R K G) (hs : N.IsSmooth) (hc : N.HasConnectedFibres) :
    RelativeComponentModelData R K G where
  full := N
  neutral := N
  full_smooth := hs
  neutral_smooth := hs
  neutral_connectedFibres := hc
  inclusion :=
    { hom := 𝟙 N.group
      generic_comm := by simp }
  isRelativeComponent :=
    { isOpenImmersion := by
        change IsOpenImmersion (𝟙 N.group.X.left)
        infer_instance
      factors_iff := by
        intro T x
        constructor
        · intro _ s
          let H := RelativeIdentityComponent.residueFiber N.group s
          let : ConnectedSpace H.X.left := hc s
          change Set.range _ ⊆ connectedComponent (IdentityComponent.identityPoint H)
          rw [PreconnectedSpace.connectedComponent_eq_univ]
          exact Set.subset_univ _
        · intro _
          exact ⟨x, Category.comp_id x⟩ }

variable {F : Type u} [Field F] [ValuativeRel F] [TopologicalSpace F]
    [IsNonarchimedeanLocalField F]
    {G : GroupScheme (Spec (CommRingCat.of (inertiaFixedField F)))}
    [IsAffineHom G.X.hom]
    (C : MaximalUnramified.BuildingData F G) (E : UnramifiedZeroDatum F G)
    (x : C.Apartment)
    (N : IntegralModel (fixedFieldIntegers F) (inertiaFixedField F) G)
    (hs : N.IsSmooth)
    (hN : N.integralPoints =
      E.zeroPoints ⊓ C.pointwiseFixer (C.apartmentMap '' {x}))
    {U : GroupScheme
      (Spec (CommRingCat.of (IsLocalRing.ResidueField (fixedFieldIntegers F))))}
    (iU : U ⟶ N.specialFibre) (hU : IsUnipotentRadical iU)

include hs hN hU in
/-- The full actual generic radical preimage intersects every root group in
the positive root fixer at the specified singleton. -/
theorem unramifiedSingletonRadical_root_intersection (a : relativeRoots C.i) :
    N.specialFibreSubgroupPoints (rationalPoints.map iU).range ⊓
        rootGroupPoints C.i a =
      C.apartment.rootFixerPlus a {x} := by
  let : Smooth N.group.X.hom := hs
  let : IsAlgClosed (IsLocalRing.ResidueField (fixedFieldIntegers F)) :=
    (fixedFieldResidueIsAlgClosure F).1
  have hc := unramifiedSingletonZeroFixer_hasConnectedFibres C E N hs x hN
  let D := selfRelativeComponent N hs hc
  let A : IntegralSplitTorusData D.neutral C.i :=
    unramifiedZeroFixerIntegralSplitTorusData C E N {x} hN
  let : Smooth N.specialFibre.X.hom :=
    inferInstanceAs (Smooth (pullback.snd N.group.X.hom
      (IntegralModel.residueBaseMap (fixedFieldIntegers F))))
  let : IsAffineHom N.specialFibre.X.hom :=
    MorphismProperty.pullback_snd _ _ N.affine
  let : ConnectedSpace N.specialFibre.X.left :=
    N.hasConnectedSpecialFibre_of_hasConnectedFibres hc
  obtain ⟨V, q, hq, hV⟩ :=
    unipotentRadicalQuotient _ N.specialFibre U iU hU
  let Q : SpecialFibreQuotientData D :=
    { radical := U
      radicalInclusion := iU
      quotient := V
      quotient_affine := hV.isAffineHom
      projection := q }
  have hQ : Q.IsReductiveQuotient :=
    ⟨hU, hq, (perfectFieldPseudoReductive _ V).mp hV⟩
  have hroot :
      (A.rootModel a a.2.1).integralPoints.map
          (rationalPoints.map (A.rootInclusion a a.2.1)) =
        N.integralPoints ⊓ rootGroupPoints C.i a :=
    A.rootModel_integralPoints_eq a a.2.1
  have hcriterion (u : (A.rootModel a a.2.1).integralSections) :
      N.reduction (rationalPoints.map (A.rootModelMap a a.2.1).hom u) ∈
          (rationalPoints.map iU).range ↔
        rationalPoints.map (A.rootInclusion a a.2.1)
            ((A.rootModel a a.2.1).integralPointMap u) ∈
          C.apartment.rootFixerPlus a {x} := by
    have h := unramifiedRootPositiveReduction F G C E {x}
      (Set.singleton_nonempty x) (fun f => by simp) D hN A Q hQ a u
    change N.reduction (rationalPoints.map (A.rootModelMap a a.2.1).hom u) ∈
      (rationalPoints.map iU).range ↔ _ at h
    simpa only [Set.mem_singleton_iff, exists_eq_left,
      C.apartment.rootFixerPlus_singleton] using h
  ext g
  constructor
  · rintro ⟨hg, hga⟩
    have hgint := N.specialFibreSubgroupPoints_le_integralPoints
      (rationalPoints.map iU).range hg
    have hgroot : g ∈ (A.rootModel a a.2.1).integralPoints.map
        (rationalPoints.map (A.rootInclusion a a.2.1)) := by
      rw [hroot]
      exact ⟨hgint, hga⟩
    obtain ⟨t, ⟨u, rfl⟩, hug⟩ := hgroot
    have hmap := (A.rootModelMap a a.2.1).integralPointMap_naturality u
    obtain ⟨v, hv, hvg⟩ := hg
    have hvu : v = rationalPoints.map (A.rootModelMap a a.2.1).hom u :=
      N.integralPointMap_injective (hvg.trans (hmap.trans hug).symm)
    have hu := (hcriterion u).mp (hvu ▸ hv)
    rwa [hug] at hu
  · intro hg
    have hgfix := C.apartment.rootFixerPlus_le_rootFixer a {x} hg
    have hgboth : g ∈ N.integralPoints ⊓ rootGroupPoints C.i a := by
      have h := rootGroupPoints_inf_unramifiedZeroFixer_eq_rootFixer C E {x} a
      rw [← h, ← hN] at hgfix
      exact ⟨hgfix.2, hgfix.1⟩
    have hgroot : g ∈ (A.rootModel a a.2.1).integralPoints.map
        (rationalPoints.map (A.rootInclusion a a.2.1)) := by
      rwa [hroot]
    obtain ⟨t, ⟨u, rfl⟩, hug⟩ := hgroot
    have hu := (hcriterion u).mpr (hug ▸ hg)
    refine ⟨⟨rationalPoints.map (A.rootModelMap a a.2.1).hom u, hu, ?_⟩, hgboth.2⟩
    exact ((A.rootModelMap a a.2.1).integralPointMap_naturality u).trans hug

/-- Singleton radical generation by positive root fixers and the actual
intersection with the represented generic torus centralizer. -/
def UnramifiedSingletonRadicalRootCentralizerGenerationStatement : Prop :=
  ∀ (F : Type u) [Field F] [ValuativeRel F] [TopologicalSpace F]
    [IsNonarchimedeanLocalField F]
    (G : GroupScheme (Spec (CommRingCat.of (inertiaFixedField F))))
    [IsAffineHom G.X.hom]
    (C : MaximalUnramified.BuildingData F G) (E : UnramifiedZeroDatum F G)
    (x : C.Apartment)
    (N : IntegralModel (fixedFieldIntegers F) (inertiaFixedField F) G),
    N.IsSmooth →
    N.integralPoints =
      E.zeroPoints ⊓ C.pointwiseFixer (C.apartmentMap '' {x}) →
    ∀ (U : GroupScheme
      (Spec (CommRingCat.of (IsLocalRing.ResidueField (fixedFieldIntegers F)))))
      (iU : U ⟶ N.specialFibre), IsUnipotentRadical iU →
      let B := N.specialFibreSubgroupPoints (rationalPoints.map iU).range
      B = (B ⊓ (rationalPoints.map C.centralizer.j).range) ⊔
        ⨆ a : relativeRoots C.i, C.apartment.rootFixerPlus a {x}

/-- The full singleton radical preimage is generated by the actual centralizer
intersection and the positive root fixers. -/
theorem unramifiedSingletonRadicalRootCentralizerGeneration :
    UnramifiedSingletonRadicalRootCentralizerGenerationStatement.{u} := by
  intro F _ _ _ _ G _ C E x N hs hN U iU hU
  let : Smooth N.group.X.hom := hs
  let : GeometricallyConnected N.group.X.hom :=
    geometricallyConnected_of_connectedFibres N
      (unramifiedSingletonZeroFixer_hasConnectedFibres C E N hs x hN)
  let A := unramifiedZeroFixerIntegralSplitTorusData C E N {x} hN
  have h := A.radicalRootCentralizerGeneration
    C.isConnectedReductive C.isMaximalSplitTorus iU hU
  change N.specialFibreSubgroupPoints (rationalPoints.map iU).range =
    (N.specialFibreSubgroupPoints (rationalPoints.map iU).range ⊓
      (torusCentralizer C.i).carrier (𝟙_ (Over _))) ⊔
      ⨆ a : relativeRoots C.i,
        N.specialFibreSubgroupPoints (rationalPoints.map iU).range ⊓
          rootGroupPoints C.i a at h
  rw [← C.centralizer.isRepresentedBy.2] at h
  simp_rw [unramifiedSingletonRadical_root_intersection C E x N hs hN iU hU] at h
  exact h

end Langlands.BruhatTits.IntegralModels
