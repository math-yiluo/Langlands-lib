/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.AlgebraicGeometry.DerivedBaseChangeMayerVietorisCanonicalData
import WeilConjectures.AlgebraicGeometry.DerivedBaseChangeMayerVietorisCanonicalShift
import WeilConjectures.AlgebraicGeometry.DerivedBaseChangeMayerVietorisCanonicalPullback
import WeilConjectures.AlgebraicGeometry.OpenImageComplexComparisonUnit
import WeilConjectures.AlgebraicGeometry.OpenImageComplexComparisonRestriction

/-! Intermediate existence data for the relative Mayer--Vietoris boundary.
Source: Stacks Project, Tags 08BV and 0DJ9.
(blueprint: lem-pc-rf-mv-base-change-connecting-square-data).
-/
@[expose] public section
universe u w
open CategoryTheory CategoryTheory.Limits TopologicalSpace Pretriangulated
set_option autoImplicit false
noncomputable section
namespace AlgebraicGeometry

variable [∀ Y : Scheme.{u},
  HasDerivedCategory.{w} (SheafOfModules.{u} (moduleRings Y.toRingedSpace))]

-- Transporting the concrete complex comparisons requires more elaboration steps.
/-- Distinguishedness for the specified SES boundary, without existential choices
of the boundary or its comparisons. Proof: identify both first arrows using the
localized units and restrictions, and the third using inverse cancellation.
Source: Stacks Tag 08BV
(blueprint: lem-pc-rf-mv-base-change-connecting-square-data). -/
private theorem pinned_boundary_distinguished (X : Scheme.{u}) (U V W : X.Opens)
    (iU : W ⟶ U) (iV : W ⟶ V) (hW : U ⊓ V = W) (hcover : U ⊔ V = ⊤)
    (K : schemeDerivedCategory X) :
    mvBaseChangeTriangle X U V W iU iV (mvOpenRestrictionAdjunction X U)
      (mvOpenRestrictionAdjunction X V) (mvOpenRestrictionAdjunction X W) K
      (mvCanonicalBoundary X U V W hW hcover K) ∈
        distTriang (schemeDerivedCategory X) := by
  subst W
  have hiU : iU = homOfLE (inf_le_left : U ⊓ V ≤ U) := Subsingleton.elim _ _
  have hiV : iV = homOfLE (inf_le_right : U ⊓ V ≤ V) := Subsingleton.elim _ _
  subst iU
  subst iV
  let I := schemeMVResolution X K
  let e := schemeMVResolutionIso X K
  let adjU := mvOpenRestrictionAdjunction X U
  let adjV := mvOpenRestrictionAdjunction X V
  let adjW := mvOpenRestrictionAdjunction X (U ⊓ V)
  let cU := schemeOpenModuleImageComplexComparison X U I adjU
  let cV := schemeOpenModuleImageComplexComparison X V I adjV
  let cW := schemeOpenModuleImageComplexComparison X (U ⊓ V) I adjW
  let tU := ((schemeOpenRestriction X U).mapDerivedCategory ⋙
    schemeDerivedDirectImage U.ι).mapIso e
  let tV := ((schemeOpenRestriction X V).mapDerivedCategory ⋙
    schemeDerivedDirectImage V.ι).mapIso e
  let tW := ((schemeOpenRestriction X (U ⊓ V)).mapDerivedCategory ⋙
    schemeDerivedDirectImage (U ⊓ V).ι).mapIso e
  let eU := cU ≪≫ tU
  let eV := cV ≪≫ tV
  let eC := cW ≪≫ tW
  have hu : DerivedCategory.Q.map (schemeOpenModuleImageComplexUnit X U I) ≫ eU.hom =
      e.hom ≫ adjU.unit.app K := by
    exact (Category.assoc _ _ _).symm.trans
      ((congrArg (fun a ↦ a ≫ tU.hom)
        (schemeOpenModuleImageComplexComparison_unit X U I adjU)).trans
          (adjU.unit.naturality e.hom).symm)
  have hv : DerivedCategory.Q.map (schemeOpenModuleImageComplexUnit X V I) ≫ eV.hom =
      e.hom ≫ adjV.unit.app K := by
    exact (Category.assoc _ _ _).symm.trans
      ((congrArg (fun a ↦ a ≫ tV.hom)
        (schemeOpenModuleImageComplexComparison_unit X V I adjV)).trans
          (adjV.unit.naturality e.hom).symm)
  have hr {A : X.Opens} (i : U ⊓ V ⟶ A) :
      DerivedCategory.Q.map (schemeOpenModuleImageComplexRestriction X i I) ≫ eC.hom =
        (mvCanonicalOpenComparison X A K).hom ≫
          schemeDerivedOpenDirectImageRestriction X i
            (mvOpenRestrictionAdjunction X A) adjW K := by
    let adjA := mvOpenRestrictionAdjunction X A
    let cA := schemeOpenModuleImageComplexComparison X A I adjA
    let tA := ((schemeOpenRestriction X A).mapDerivedCategory ⋙
      schemeDerivedDirectImage A.ι).mapIso e
    have hn : schemeDerivedOpenDirectImageRestriction X i adjA adjW
        (DerivedCategory.Q.obj I) ≫ tW.hom = tA.hom ≫
          schemeDerivedOpenDirectImageRestriction X i adjA adjW K := by
      let F := (schemeOpenRestriction X A).mapDerivedCategory
      let G := schemeDerivedDirectImage A.ι
      let H := (schemeOpenRestriction X (U ⊓ V)).mapDerivedCategory
      let T := (schemeOpenOverlapRestriction X i).mapDerivedCategory
      let α := schemeDerivedOpenRestrictionCompIso X i
      let ρ : F ⋙ G ⟶ H ⋙ schemeDerivedDirectImage (U ⊓ V).ι :=
        Functor.whiskerLeft (F ⋙ G) adjW.unit ≫
          Functor.whiskerRight
            (Functor.whiskerLeft (F ⋙ G) α.inv ≫
              Functor.whiskerRight (Functor.whiskerLeft F adjA.counit) T ≫ α.hom)
            (schemeDerivedDirectImage (U ⊓ V).ι)
      simpa only [schemeDerivedOpenDirectImageRestriction, ρ, tA, tW,
        Functor.mapIso_hom, NatTrans.comp_app, Functor.whiskerLeft_app,
        Functor.whiskerRight_app, Functor.comp_map, Functor.comp_obj,
        Adjunction.homEquiv_unit] using (ρ.naturality e.hom).symm
    exact (Category.assoc _ _ _).symm.trans
      ((congrArg (fun a ↦ a ≫ tW.hom)
        (schemeOpenModuleImageComplexComparison_restriction X i I adjA adjW)).trans
        ((Category.assoc _ _ _).trans
          ((congrArg (fun a ↦ cA.hom ≫ a) hn).trans (Category.assoc _ _ _).symm)))
  let Q : CochainComplex (SheafOfModules.{u} (moduleRings X.toRingedSpace)) ℤ ⥤
      schemeDerivedCategory X := DerivedCategory.Q
  have : PreservesBinaryBiproducts Q :=
    preservesBinaryBiproducts_of_preservesBiproducts Q
  let eB := Q.mapBiprod (schemeOpenModuleImageComplex X U I)
    (schemeOpenModuleImageComplex X V I) ≪≫ biprod.mapIso eU eV
  let hS := schemeMayerVietorisComplex_shortExact X U V hcover I
    (fun _ ↦ inferInstance)
  apply isomorphic_distinguished _ (DerivedCategory.triangleOfSES_distinguished hS)
  refine (Triangle.isoMk _ _ e eB eC ?_ ?_ ?_).symm
  · change Q.map (schemeMayerVietorisF X U V I) ≫ eB.hom = _
    dsimp only [mvBaseChangeTriangle, Triangle.mk_mor₁,
      schemeMayerVietorisF, eB, Iso.trans_hom, biprod.mapIso]
    rw [← Category.assoc, biprod.map_lift_mapBiprod]
    apply biprod.hom_ext
    · simp only [Category.assoc, biprod.map_fst]
      rw [← Category.assoc, biprod.lift_fst]
      simpa [Category.assoc] using hu
    · simp only [Category.assoc, biprod.map_snd]
      rw [← Category.assoc, biprod.lift_snd]
      simpa [Category.assoc] using hv
  · change Q.map (schemeMayerVietorisG X U V I) ≫ eC.hom = _
    dsimp only [mvBaseChangeTriangle, Triangle.mk_mor₂,
      schemeMayerVietorisG, eB, Iso.trans_hom, biprod.mapIso]
    rw [← biprod.mapBiprod_hom_desc Q]
    simp only [Category.assoc]
    apply congrArg (fun a ↦ (Q.mapBiprod
      (schemeOpenModuleImageComplex X U I) (schemeOpenModuleImageComplex X V I)).hom ≫ a)
    apply biprod.hom_ext'
    · simpa only [Category.assoc, Triangle.mk_mor₂, biprod.inl_desc_assoc,
        biprod.inl_map_assoc, biprod.inl_desc, mvCanonicalOpenComparison, eU, cU, tU,
        Iso.trans_hom, adjU, adjW, I, e] using hr (homOfLE (inf_le_left : U ⊓ V ≤ U))
    · simpa only [Category.assoc, Triangle.mk_mor₂, biprod.inr_desc_assoc,
        biprod.inr_map_assoc, biprod.inr_desc, Functor.map_neg,
        mvCanonicalOpenComparison, eV, cV, tV,
        Iso.trans_hom, adjV, adjW, I, e, Preadditive.comp_neg, Preadditive.neg_comp]
        using congrArg Neg.neg (hr (homOfLE (inf_le_right : U ⊓ V ≤ V)))
  · change DerivedCategory.triangleOfSESδ hS ≫ e.hom⟦(1 : ℤ)⟧' =
      eC.hom ≫ (eC.inv ≫ DerivedCategory.triangleOfSESδ hS ≫ e.hom⟦(1 : ℤ)⟧')
    simp only [Iso.hom_inv_id_assoc]

/-- The explicit SES boundaries are distinguished, and their images are distinguished
for the specified adjunction-compatible derived-functor shifts. The actual unit/counit
shift compatibility is proved in mvCanonicalPullbackShift_compatible.
Source: Stacks Tags 08BV and 0DJ9
(blueprint: lem-pc-rf-mv-base-change-connecting-square-data). -/
theorem mvBoundary_canonical_data
    {X S X' S' : Scheme.{u}} [IsAffine S] [IsAffine S']
    (f : X ⟶ S) (f' : X' ⟶ S') (g : S' ⟶ S) (g' : X' ⟶ X)
    [QuasiCompact f] [QuasiSeparated f]
    (K : schemeDerivedCategory X) (K' : schemeDerivedCategory X')
    (U V : X.Opens) (hcover : U ⊔ V = ⊤) :
    let δ := mvCanonicalBoundary X U V (U ⊓ V) rfl hcover K
    let δ' := mvCanonicalBoundary X' (g' ⁻¹ᵁ U) (g' ⁻¹ᵁ V) (g' ⁻¹ᵁ (U ⊓ V))
      (Scheme.Hom.preimage_inf g').symm
      (by rw [← Scheme.Hom.preimage_sup, hcover, Scheme.Hom.preimage_top]) K'
    let csF := mvCanonicalSourceShift f g
    let csG := mvCanonicalTargetShift f'
      let T := mvBaseChangeTriangle X U V (U ⊓ V) (homOfLE inf_le_left)
        (homOfLE inf_le_right) (mvOpenRestrictionAdjunction X U)
        (mvOpenRestrictionAdjunction X V) (mvOpenRestrictionAdjunction X (U ⊓ V)) K δ
      let T' := mvBaseChangeTriangle X' (g' ⁻¹ᵁ U) (g' ⁻¹ᵁ V)
        (g' ⁻¹ᵁ (U ⊓ V)) ((Opens.map g'.base).map (homOfLE (inf_le_left : U ⊓ V ≤ U)))
        ((Opens.map g'.base).map (homOfLE (inf_le_right : U ⊓ V ≤ V)))
        (mvOpenRestrictionAdjunction X' (g' ⁻¹ᵁ U))
        (mvOpenRestrictionAdjunction X' (g' ⁻¹ᵁ V))
        (mvOpenRestrictionAdjunction X' (g' ⁻¹ᵁ (U ⊓ V))) K' δ'
      T ∈ distTriang (schemeDerivedCategory X) ∧
      T' ∈ distTriang (schemeDerivedCategory X') ∧
      (@Functor.mapTriangle _ _ _ _ _ _
        (schemeDerivedDirectImage f ⋙ derivedPullback g) csF).obj T ∈
        distTriang (schemeDerivedCategory S') ∧
      (@Functor.mapTriangle _ _ _ _ _ _ (schemeDerivedDirectImage f') csG).obj T' ∈
        distTriang (schemeDerivedCategory S') := by
  dsimp only
  have hT := pinned_boundary_distinguished X U V (U ⊓ V)
    (homOfLE inf_le_left) (homOfLE inf_le_right) rfl hcover K
  have hcover' : (g' ⁻¹ᵁ U) ⊔ (g' ⁻¹ᵁ V) = ⊤ := by
    rw [← Scheme.Hom.preimage_sup, hcover, Scheme.Hom.preimage_top]
  have hT' := pinned_boundary_distinguished X' (g' ⁻¹ᵁ U) (g' ⁻¹ᵁ V)
    (g' ⁻¹ᵁ (U ⊓ V))
    ((Opens.map g'.base).map (homOfLE (inf_le_left : U ⊓ V ≤ U)))
    ((Opens.map g'.base).map (homOfLE (inf_le_right : U ⊓ V ≤ V)))
    (Scheme.Hom.preimage_inf g').symm hcover' K'
  let := mvCanonicalPullbackShift g
  let := mvCanonicalPullbackShift_triangulated g
  refine ⟨hT, hT', ?_, ?_⟩
  · exact (schemeDerivedDirectImage f ⋙ derivedPullback g).map_distinguished _ hT
  · exact (schemeDerivedDirectImage f').map_distinguished _ hT'

/-- Compatibility of the specifically constructed SES boundaries for the specifically
constructed adjunction-compatible shifts. There are no arbitrary boundary or shift
parameters: each side refers to the same fixed SES and right-derived shift data
used by mvBoundary_canonical_data.
Source: Stacks Project, Tags 08BV, 08HY and 0DJ9.
(blueprint: lem-pc-rf-mv-base-change-connecting-square-equation).

Proof: transpose ψ under the pinned pullback/direct-image adjunction. Represent this
map by a chain map into the K-injective resolution of the direct image of K'. Its
restrictions form a morphism from the source cover SES to the termwise direct image
of the target cover SES. The target SES is degreewise split, so its direct-image
boundary is the right-derived image of triangleOfSESδ with the existing right-derived
shift. Apply triangleOfSESδ_naturality and transport by mvCanonicalOpenComparison
and schemeMVResolutionIso. The adjunction units and counits defining these comparisons
identify the overlap map with the transpose of mvBaseChangeOpenMap. The direct-image
composition maps are the mates of the pinned derived-pullback compositions; their
right-derived unit equations identify the chain-level comparisons. Finally apply Rf_*
and transpose under the pinned adjunction for g. Its unit and counit commute with
shifts by mvCanonicalPullbackShift_compatible, and the composite source shift is
mvCanonicalSourceShift. Thus transposition carries precisely the right-derived
connecting equation to the displayed equality, with no independent sign choice. -/
theorem mvBoundary_equation
    {X S X' S' : Scheme.{u}} [IsAffine S] [IsAffine S']
    (f : X ⟶ S) (f' : X' ⟶ S') (g : S' ⟶ S) (g' : X' ⟶ X)
    [QuasiCompact f] [QuasiSeparated f] (hsq : IsPullback g' f' f g)
    (K : schemeDerivedCategory X) (K' : schemeDerivedCategory X')
    (U V : X.Opens) (hcover : U ⊔ V = ⊤)
    (ψ : (derivedPullback g').obj K ⟶ K') :
    let δ := mvCanonicalBoundary X U V (U ⊓ V) rfl hcover K
    let δ' := mvCanonicalBoundary X' (g' ⁻¹ᵁ U) (g' ⁻¹ᵁ V) (g' ⁻¹ᵁ (U ⊓ V))
      (Scheme.Hom.preimage_inf g').symm
      (by rw [← Scheme.Hom.preimage_sup, hcover, Scheme.Hom.preimage_top]) K'
    let csF := mvCanonicalSourceShift f g
    let csG := mvCanonicalTargetShift f'
    (schemeDerivedDirectImage f ⋙ derivedPullback g).map δ ≫
        (letI := csF;
          (schemeDerivedDirectImage f ⋙ derivedPullback g).commShiftIso (1 : ℤ)).hom.app K ≫
        (schemeDerivedBaseChangeMap f f' g g' hsq.w K ≫
          (schemeDerivedDirectImage f').map ψ)⟦(1 : ℤ)⟧' =
      mvBaseChangeOpenMap f f' g g' hsq.w K K' ψ (U ⊓ V) ≫
        (schemeDerivedDirectImage f').map δ' ≫
        (letI := csG; (schemeDerivedDirectImage f').commShiftIso (1 : ℤ)).hom.app K' := by
  dsimp only
  let := mvCanonicalPullbackShift g'
  rw [mvCanonicalBaseChange_shift f f' g g' hsq.w _ K K' ψ (1 : ℤ)]
  rw [mvCanonicalBoundary_pullback g' K K' ψ U V hcover]
  simp only [mvBaseChangeOpenMap, Functor.map_comp, Category.assoc]

end AlgebraicGeometry
