/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.AlgebraicGeometry.PerfectHomTransport


public import WeilConjectures.AlgebraicGeometry.PerfectOverlapHomContinuityData
public import WeilConjectures.AlgebraicGeometry.PerfectOverlapObjectRealizationCoreBase
public import WeilConjectures.AlgebraicGeometry.PerfectHomTransportExtension
public import WeilConjectures.AlgebraicGeometry.PerfectOverlapStageEquivalence
public import WeilConjectures.AlgebraicGeometry.DerivedOpenRestrictionLocalization
public import WeilConjectures.AlgebraicGeometry.SingleComplexOpenRestrictionData
public import WeilConjectures.AlgebraicGeometry.SingleComplexOpenCounitCompatibility
import WeilConjectures.AlgebraicGeometry.DerivedPullbackComposition
import WeilConjectures.AlgebraicGeometry.TwoOpenComparisonDiagram
import WeilConjectures.AlgebraicGeometry.DerivedOpenRestrictionIsoDescent
import WeilConjectures.AlgebraicGeometry.PerfectOverlapSiteCancellationAbstract

/-! # Core object comparison data (without the final Hom pin).

Source: Stacks Project, Tags 09RE, 08DW and 0D5S.
(blueprint: lem-pc-perfect-overlap-object-realization-core-data).
-/

@[expose] public section

set_option autoImplicit false
set_option synthInstance.maxSize 2048
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

universe u w v h v' h'
open CategoryTheory CategoryTheory.Limits
namespace AlgebraicGeometry

attribute [local instance] Functor.additive_of_preserves_binary_products
attribute [local instance 2000] openComparisonModuleAbelian openComparisonOverModuleAbelian

private theorem cancel_iso_pasting {C : Type*} [Category C]
    {A B D E : C} (f : A ⟶ B) (s : D ≅ B)
    (g : D ⟶ E) (h : E ⟶ D) (gh : g ≫ h = 𝟙 D) :
    f = 𝟙 A ≫ f ≫ s.inv ≫ g ≫ 𝟙 E ≫ h ≫ s.hom := by
  simp only [Category.id_comp, Category.comp_id,
    ← Category.assoc, gh, Category.comp_id, Iso.inv_hom_id]
section

/-- Lift the two overlap comparisons through localization of the restriction functors.
The inverse restrictions of beta, tau, betaW and alpha define the whiskered comparison;
`map_preimage` and cancellation give the two required coherence equations. -/
noncomputable def comparisonFromRestrictions
    {C D A B W P Q T : Type*}
    [Category* C] [Category* D] [Category* A] [Category* B]
    [Category* W] [Category* P] [Category* Q] [Category* T]
    (L : C ⥤ D) (TU : C ⥤ A) (TV : C ⥤ B) (TW : C ⥤ W)
    (SU : A ⥤ W) (SV : B ⥤ W)
    (RU : D ⥤ P) (RV : D ⥤ Q) (RW : D ⥤ T)
    (SP : P ⥤ T) (SQ : Q ⥤ T)
    (αU : TU ⋙ SU ≅ TW) (αV : TV ⋙ SV ≅ TW)
    (τU : RU ⋙ SP ≅ RW) (τV : RV ⋙ SQ ≅ RW)
    [((Functor.whiskeringLeft C A T).obj TU).Full]
    [((Functor.whiskeringLeft C A T).obj TU).Faithful]
    [((Functor.whiskeringLeft C B T).obj TV).Full]
    [((Functor.whiskeringLeft C B T).obj TV).Faithful]
    (HU : A ⥤ P) (HV : B ⥤ Q) (HW : W ⥤ T)
    (βU : L ⋙ RU ≅ TU ⋙ HU) (βV : L ⋙ RV ≅ TV ⋙ HV)
    (βW : L ⋙ RW ≅ TW ⋙ HW) :
    TwoOpenComparisonDiagram L TU TV TW SU SV RU RV RW SP SQ αU αV τU τV := by
  let δU : TU ⋙ (HU ⋙ SP) ≅ TU ⋙ (SU ⋙ HW) :=
    (Functor.associator _ _ _).symm ≪≫
      Functor.isoWhiskerRight βU.symm SP ≪≫ Functor.associator _ _ _ ≪≫
      Functor.isoWhiskerLeft L τU ≪≫ βW ≪≫
      Functor.isoWhiskerRight αU.symm HW ≪≫ Functor.associator _ _ _
  let δV : TV ⋙ (HV ⋙ SQ) ≅ TV ⋙ (SV ⋙ HW) :=
    (Functor.associator _ _ _).symm ≪≫
      Functor.isoWhiskerRight βV.symm SQ ≪≫ Functor.associator _ _ _ ≪≫
      Functor.isoWhiskerLeft L τV ≪≫ βW ≪≫
      Functor.isoWhiskerRight αV.symm HW ≪≫ Functor.associator _ _ _
  let γU := ((Functor.whiskeringLeft C A T).obj TU).preimageIso δU
  let γV := ((Functor.whiskeringLeft C B T).obj TV).preimageIso δV
  have hγU (F : C) : γU.hom.app (TU.obj F) = δU.hom.app F :=
    congrArg (fun a ↦ a.app F)
      (((Functor.whiskeringLeft C A T).obj TU).map_preimage δU.hom)
  have hγV (F : C) : γV.hom.app (TV.obj F) = δV.hom.app F :=
    congrArg (fun a ↦ a.app F)
      (((Functor.whiskeringLeft C B T).obj TV).map_preimage δV.hom)
  refine ⟨HU, HV, HW, βU, βV, βW, γU, γV, ?_, ?_⟩
  · intro F
    rw [hγU]
    simp [δU]
  · intro F
    rw [hγV]
    simp [δV]

/-- The first localization-lifted comparison evaluated on a restricted object.
Source: Stacks Project, Tag 08DW. The lifted isomorphism is the preimage of
the composite of the first-open comparison, the site restriction comparison,
the intersection comparison, and the inverse open restriction comparison.
Whiskering the preimage back along `TU` recovers that composite exactly. -/
theorem comparisonFromRestrictions_gammaU_on_image
    {C D A B W P Q T : Type*}
    [Category* C] [Category* D] [Category* A] [Category* B]
    [Category* W] [Category* P] [Category* Q] [Category* T]
    (L : C ⥤ D) (TU : C ⥤ A) (TV : C ⥤ B) (TW : C ⥤ W)
    (SU : A ⥤ W) (SV : B ⥤ W)
    (RU : D ⥤ P) (RV : D ⥤ Q) (RW : D ⥤ T)
    (SP : P ⥤ T) (SQ : Q ⥤ T)
    (αU : TU ⋙ SU ≅ TW) (αV : TV ⋙ SV ≅ TW)
    (τU : RU ⋙ SP ≅ RW) (τV : RV ⋙ SQ ≅ RW)
    [((Functor.whiskeringLeft C A T).obj TU).Full]
    [((Functor.whiskeringLeft C A T).obj TU).Faithful]
    [((Functor.whiskeringLeft C B T).obj TV).Full]
    [((Functor.whiskeringLeft C B T).obj TV).Faithful]
    (HU : A ⥤ P) (HV : B ⥤ Q) (HW : W ⥤ T)
    (βU : L ⋙ RU ≅ TU ⋙ HU) (βV : L ⋙ RV ≅ TV ⋙ HV)
    (βW : L ⋙ RW ≅ TW ⋙ HW) (F : C) :
    let δU : TU ⋙ (HU ⋙ SP) ≅ TU ⋙ (SU ⋙ HW) :=
      (Functor.associator _ _ _).symm ≪≫
        Functor.isoWhiskerRight βU.symm SP ≪≫ Functor.associator _ _ _ ≪≫
        Functor.isoWhiskerLeft L τU ≪≫ βW ≪≫
        Functor.isoWhiskerRight αU.symm HW ≪≫ Functor.associator _ _ _
    ((comparisonFromRestrictions L TU TV TW SU SV RU RV RW SP SQ
      αU αV τU τV HU HV HW βU βV βW).γU).hom.app (TU.obj F) =
      δU.hom.app F := by
  let δU : TU ⋙ (HU ⋙ SP) ≅ TU ⋙ (SU ⋙ HW) :=
    (Functor.associator _ _ _).symm ≪≫
      Functor.isoWhiskerRight βU.symm SP ≪≫ Functor.associator _ _ _ ≪≫
      Functor.isoWhiskerLeft L τU ≪≫ βW ≪≫
      Functor.isoWhiskerRight αU.symm HW ≪≫ Functor.associator _ _ _
  change (((Functor.whiskeringLeft C A T).obj TU).preimageIso δU).hom.app
    (TU.obj F) = δU.hom.app F
  rw [Functor.preimageIso_hom]
  exact congrArg (fun a ↦ a.app F)
    (((Functor.whiskeringLeft C A T).obj TU).map_preimage δU.hom)

/-- The second localization-lifted comparison evaluated on a restricted object.
Source: Stacks Project, Tag 08DW. Whiskering the lifted second-open
isomorphism along `TV` recovers the composite of the second-open comparison,
the site restriction comparison, the intersection comparison, and the inverse
open restriction comparison. -/
theorem comparisonFromRestrictions_gammaV_on_image
    {C D A B W P Q T : Type*}
    [Category* C] [Category* D] [Category* A] [Category* B]
    [Category* W] [Category* P] [Category* Q] [Category* T]
    (L : C ⥤ D) (TU : C ⥤ A) (TV : C ⥤ B) (TW : C ⥤ W)
    (SU : A ⥤ W) (SV : B ⥤ W)
    (RU : D ⥤ P) (RV : D ⥤ Q) (RW : D ⥤ T)
    (SP : P ⥤ T) (SQ : Q ⥤ T)
    (αU : TU ⋙ SU ≅ TW) (αV : TV ⋙ SV ≅ TW)
    (τU : RU ⋙ SP ≅ RW) (τV : RV ⋙ SQ ≅ RW)
    [((Functor.whiskeringLeft C A T).obj TU).Full]
    [((Functor.whiskeringLeft C A T).obj TU).Faithful]
    [((Functor.whiskeringLeft C B T).obj TV).Full]
    [((Functor.whiskeringLeft C B T).obj TV).Faithful]
    (HU : A ⥤ P) (HV : B ⥤ Q) (HW : W ⥤ T)
    (βU : L ⋙ RU ≅ TU ⋙ HU) (βV : L ⋙ RV ≅ TV ⋙ HV)
    (βW : L ⋙ RW ≅ TW ⋙ HW) (F : C) :
    let δV : TV ⋙ (HV ⋙ SQ) ≅ TV ⋙ (SV ⋙ HW) :=
      (Functor.associator _ _ _).symm ≪≫
        Functor.isoWhiskerRight βV.symm SQ ≪≫ Functor.associator _ _ _ ≪≫
        Functor.isoWhiskerLeft L τV ≪≫ βW ≪≫
        Functor.isoWhiskerRight αV.symm HW ≪≫ Functor.associator _ _ _
    ((comparisonFromRestrictions L TU TV TW SU SV RU RV RW SP SQ
      αU αV τU τV HU HV HW βU βV βW).γV).hom.app (TV.obj F) =
      δV.hom.app F := by
  let δV : TV ⋙ (HV ⋙ SQ) ≅ TV ⋙ (SV ⋙ HW) :=
    (Functor.associator _ _ _).symm ≪≫
      Functor.isoWhiskerRight βV.symm SQ ≪≫ Functor.associator _ _ _ ≪≫
      Functor.isoWhiskerLeft L τV ≪≫ βW ≪≫
      Functor.isoWhiskerRight αV.symm HW ≪≫ Functor.associator _ _ _
  change (((Functor.whiskeringLeft C B T).obj TV).preimageIso δV).hom.app
    (TV.obj F) = δV.hom.app F
  rw [Functor.preimageIso_hom]
  exact congrArg (fun a ↦ a.app F)
    (((Functor.whiskeringLeft C B T).obj TV).map_preimage δV.hom)

/-- Evaluate a natural isomorphism at an object transported from a known component.
Source: Stacks Project, Tag 08DW, functoriality of open restriction. Naturality
along the isomorphism identifies the two components after mapping its forward
arrow. Precompose with the mapped inverse and cancel the mapped inverse-forward
composite to obtain the displayed conjugation. -/
theorem overlapNatIso_hom_app_of_iso
    {A T : Type*} [Category* A] [Category* T]
    (H K : A ⥤ T) (γ : H ≅ K) {x y : A} (e : x ≅ y) :
    γ.hom.app y = H.map e.inv ≫ γ.hom.app x ≫ K.map e.hom := by
  calc
    γ.hom.app y = H.map (𝟙 y) ≫ γ.hom.app y := by simp
    _ = H.map (e.inv ≫ e.hom) ≫ γ.hom.app y := by rw [e.inv_hom_id]
    _ = H.map e.inv ≫ (H.map e.hom ≫ γ.hom.app y) := by
      simp only [Functor.map_comp, Category.assoc]
    _ = H.map e.inv ≫ (γ.hom.app x ≫ K.map e.hom) := by
      rw [γ.hom.naturality e.hom]
    _ = H.map e.inv ≫ γ.hom.app x ≫ K.map e.hom := by
      simp only

/-- The inverse component satisfies the same naturality transport equation.
Source: Stacks Project, Tag 08DW. Apply the forward equation to the inverse
natural isomorphism, whose source and target functors are interchanged. -/
theorem overlapNatIso_inv_app_of_iso
    {A T : Type*} [Category* A] [Category* T]
    (H K : A ⥤ T) (γ : H ≅ K) {x y : A} (e : x ≅ y) :
    γ.inv.app y = K.map e.inv ≫ γ.inv.app x ≫ H.map e.hom := by
  exact overlapNatIso_hom_app_of_iso K H γ.symm e

/-- The first open-site comparison at any object is determined by its
localization-lifted component on a restricted object.
Source: Stacks Project, Tag 08DW. Transport the inverse comparison along an
isomorphism from a restricted object by naturality. On that restricted object,
the defining preimage equation identifies it with the inverse of the explicit
comparison through `βU`, `τU`, `βW`, and `αU`. -/
theorem comparisonFromRestrictions_gammaU_inv_at_iso
    {C D A B W P Q T : Type*}
    [Category* C] [Category* D] [Category* A] [Category* B]
    [Category* W] [Category* P] [Category* Q] [Category* T]
    (L : C ⥤ D) (TU : C ⥤ A) (TV : C ⥤ B) (TW : C ⥤ W)
    (SU : A ⥤ W) (SV : B ⥤ W)
    (RU : D ⥤ P) (RV : D ⥤ Q) (RW : D ⥤ T)
    (SP : P ⥤ T) (SQ : Q ⥤ T)
    (αU : TU ⋙ SU ≅ TW) (αV : TV ⋙ SV ≅ TW)
    (τU : RU ⋙ SP ≅ RW) (τV : RV ⋙ SQ ≅ RW)
    [((Functor.whiskeringLeft C A T).obj TU).Full]
    [((Functor.whiskeringLeft C A T).obj TU).Faithful]
    [((Functor.whiskeringLeft C B T).obj TV).Full]
    [((Functor.whiskeringLeft C B T).obj TV).Faithful]
    (HU : A ⥤ P) (HV : B ⥤ Q) (HW : W ⥤ T)
    (βU : L ⋙ RU ≅ TU ⋙ HU) (βV : L ⋙ RV ≅ TV ⋙ HV)
    (βW : L ⋙ RW ≅ TW ⋙ HW)
    (F : C) {A' : A} (e : TU.obj F ≅ A') :
    let d := comparisonFromRestrictions L TU TV TW SU SV RU RV RW SP SQ
      αU αV τU τV HU HV HW βU βV βW
    let δU : TU ⋙ (HU ⋙ SP) ≅ TU ⋙ (SU ⋙ HW) :=
      (Functor.associator _ _ _).symm ≪≫
        Functor.isoWhiskerRight βU.symm SP ≪≫ Functor.associator _ _ _ ≪≫
        Functor.isoWhiskerLeft L τU ≪≫ βW ≪≫
        Functor.isoWhiskerRight αU.symm HW ≪≫ Functor.associator _ _ _
    d.γU.inv.app A' =
      (SU ⋙ d.HW).map e.inv ≫ δU.inv.app F ≫ (d.HU ⋙ SP).map e.hom := by
  let d := comparisonFromRestrictions L TU TV TW SU SV RU RV RW SP SQ
    αU αV τU τV HU HV HW βU βV βW
  let δU : TU ⋙ (HU ⋙ SP) ≅ TU ⋙ (SU ⋙ HW) :=
    (Functor.associator _ _ _).symm ≪≫
      Functor.isoWhiskerRight βU.symm SP ≪≫ Functor.associator _ _ _ ≪≫
      Functor.isoWhiskerLeft L τU ≪≫ βW ≪≫
      Functor.isoWhiskerRight αU.symm HW ≪≫ Functor.associator _ _ _
  have hImage : d.γU.hom.app (TU.obj F) = δU.hom.app F :=
    comparisonFromRestrictions_gammaU_on_image L TU TV TW SU SV
      RU RV RW SP SQ αU αV τU τV HU HV HW βU βV βW F
  have hInv : d.γU.inv.app (TU.obj F) = δU.inv.app F :=
    (Iso.inv_eq_inv (d.γU.app (TU.obj F)) (δU.app F)).2 hImage
  change d.γU.inv.app A' =
    (SU ⋙ HW).map e.inv ≫ δU.inv.app F ≫ (HU ⋙ SP).map e.hom
  rw [overlapNatIso_inv_app_of_iso (d.HU ⋙ SP) (SU ⋙ d.HW) d.γU e, hInv]
  rfl

variable [∀ Z : Scheme.{u},
  HasDerivedCategory.{w} (SheafOfModules.{u} (moduleRings Z.toRingedSpace))]
variable [∀ (Z : Scheme.{u}) (U : Z.Opens),
  HasDerivedCategory.{w} (SheafOfModules.{u} ((moduleRings Z.toRingedSpace).over U))]

/-- The inverse site equivalence with its module universe fixed. -/
noncomputable abbrev overlapSiteInverse {X : Scheme.{u}} (U : X.Opens) :
    SheafOfModules.{u} (moduleRings U.toScheme.toRingedSpace) ⥤
      SheafOfModules.{u} ((moduleRings X.toRingedSpace).over U) :=
  (Scheme.Modules.overEquiv U).inverse

/-- Natural comparison between the canonical open-site overlap functor and the
scheme pullback at the next stage. The open-site equivalence cancels by its
counit; the remaining functors agree by the cartesian component equation and
the fixed composition comparisons for derived pullback. -/
noncomputable def perfectOverlapNaturalComparisonOfSquare
    {X Y K C T S : Scheme.{u}}
    (g : X ⟶ Y) (f : K ⟶ Y)
    (pX : X ⟶ C) (pK : K ⟶ T) (pY : Y ⟶ S)
    (b : C ⟶ S) (q : T ⟶ S)
    (hg : IsPullback g pX pY b) (hf : IsPullback f pK pY q)
    (U V : Y.Opens)
    (r : (g ⁻¹ᵁ (U ⊓ V)).toScheme ⟶ (f ⁻¹ᵁ (U ⊓ V)).toScheme)
    (m : pullback ((U ⊓ V).ι ≫ pY) b ⟶
      pullback ((U ⊓ V).ι ≫ pY) q)
    (hmap :
      ((isPullback_morphismRestrict g (U ⊓ V)).paste_vert hg).isoPullback.inv ≫ r =
        m ≫ ((isPullback_morphismRestrict f (U ⊓ V)).paste_vert hf).isoPullback.inv) :
    (derivedPullback r ⋙
        (overlapSiteInverse (g ⁻¹ᵁ (U ⊓ V))).mapDerivedCategory) ⋙
      (perfectOverlapApexEquivalence g pX pY b hg U V).functor ≅
    (perfectOverlapStageEquivalence f pK pY q hf U V).functor ⋙
      derivedPullback m := by
  let Wg := g ⁻¹ᵁ (U ⊓ V)
  let eY := ((isPullback_morphismRestrict g (U ⊓ V)).paste_vert hg).isoPullback
  let eK := ((isPullback_morphismRestrict f (U ⊓ V)).paste_vert hf).isoPullback
  let := openComparisonOverModuleAbelian X.toRingedSpace Wg
  letI := openComparisonModuleAbelian Wg.toScheme.toRingedSpace
  let site : SheafOfModules.{u} ((moduleRings X.toRingedSpace).over Wg) ≌
      SheafOfModules.{u} (moduleRings Wg.toScheme.toRingedSpace) :=
    Scheme.Modules.overEquiv Wg
  let : site.functor.IsEquivalence := site.isEquivalence_functor
  let : site.inverse.IsEquivalence := site.isEquivalence_inverse
  let : site.functor.Additive := Functor.additive_of_preserves_binary_products _
  let : site.inverse.Additive := Functor.additive_of_preserves_binary_products _
  let cancel := site.mapDerivedCategory.counitIso
  change (derivedPullback r ⋙ site.inverse.mapDerivedCategory) ⋙
    (site.functor.mapDerivedCategory ⋙ derivedPullback eY.inv) ≅
    derivedPullback eK.inv ⋙ derivedPullback m
  exact Functor.associator _ _ _ ≪≫
    Functor.isoWhiskerLeft (derivedPullback r) (Functor.associator _ _ _).symm ≪≫
    Functor.isoWhiskerLeft (derivedPullback r)
      (Functor.isoWhiskerRight cancel (derivedPullback eY.inv)) ≪≫
    Functor.isoWhiskerLeft (derivedPullback r) (Functor.leftUnitor _) ≪≫
    perfectOverlapDerivedPullbackTransport r eY eK m hmap

/-- The component of the natural overlap comparison is the site counit
followed by the cartesian pullback transport. -/
theorem perfectOverlapNaturalComparisonOfSquare_hom_app
    {X Y K C T S : Scheme.{u}}
    (g : X ⟶ Y) (f : K ⟶ Y)
    (pX : X ⟶ C) (pK : K ⟶ T) (pY : Y ⟶ S)
    (b : C ⟶ S) (q : T ⟶ S)
    (hg : IsPullback g pX pY b) (hf : IsPullback f pK pY q)
    (U V : Y.Opens)
    (r : (g ⁻¹ᵁ (U ⊓ V)).toScheme ⟶ (f ⁻¹ᵁ (U ⊓ V)).toScheme)
    (m : pullback ((U ⊓ V).ι ≫ pY) b ⟶
      pullback ((U ⊓ V).ι ≫ pY) q)
    (hmap :
      ((isPullback_morphismRestrict g (U ⊓ V)).paste_vert hg).isoPullback.inv ≫ r =
        m ≫ ((isPullback_morphismRestrict f (U ⊓ V)).paste_vert hf).isoPullback.inv)
    (M : schemeDerivedCategory (f ⁻¹ᵁ U ⊓ f ⁻¹ᵁ V).toScheme) :
    let W := g ⁻¹ᵁ (U ⊓ V)
    let site : SheafOfModules.{u} ((moduleRings X.toRingedSpace).over W) ≌
      SheafOfModules.{u} (moduleRings W.toScheme.toRingedSpace) :=
      Scheme.Modules.overEquiv W
    let eY := ((isPullback_morphismRestrict g (U ⊓ V)).paste_vert hg).isoPullback
    let eK := ((isPullback_morphismRestrict f (U ⊓ V)).paste_vert hf).isoPullback
    (perfectOverlapNaturalComparisonOfSquare g f pX pK pY b q hg hf U V r m hmap).hom.app M =
      (derivedPullback eY.inv).map
        (site.mapDerivedCategory.counitIso.hom.app ((derivedPullback r).obj M)) ≫
      (perfectOverlapDerivedPullbackTransport r eY eK m hmap).hom.app M := by
  intro W site eY eK
  let := openComparisonOverModuleAbelian X.toRingedSpace W
  let := openComparisonModuleAbelian W.toScheme.toRingedSpace
  let : site.functor.IsEquivalence := site.isEquivalence_functor
  let : site.inverse.IsEquivalence := site.isEquivalence_inverse
  let : site.functor.Additive := Functor.additive_of_preserves_binary_products _
  let : site.inverse.Additive := Functor.additive_of_preserves_binary_products _
  unfold perfectOverlapNaturalComparisonOfSquare
  exact counit_comparison_component (derivedPullback r)
    site.inverse.mapDerivedCategory site.functor.mapDerivedCategory
    (derivedPullback eY.inv) (derivedPullback eK.inv ⋙ derivedPullback m)
    site.mapDerivedCategory.counitIso
    (perfectOverlapDerivedPullbackTransport r eY eK m hmap) M

/-- Exact restriction followed by the inverse site equivalence returns to the over-site.
Use the derived site equivalence's unit and the exact-functor composition comparison. -/
noncomputable def openSiteReturnIso (X : Scheme.{u}) (U : X.Opens) :
    (schemeOpenRestriction X U).mapDerivedCategory ⋙
      (overlapSiteInverse U).mapDerivedCategory ≅
        (SheafOfModules.overFunctor.{u} (moduleRings X.toRingedSpace) U).mapDerivedCategory := by
  let e : SheafOfModules.{u} ((moduleRings X.toRingedSpace).over U) ≌
      SheafOfModules.{u} (moduleRings U.toScheme.toRingedSpace) := Scheme.Modules.overEquiv U
  exact Functor.isoWhiskerRight
      (Functor.mapDerivedCategoryCompIso _ _).symm _ ≪≫
    Functor.associator _ _ _ ≪≫
    Functor.isoWhiskerLeft _ e.mapDerivedCategory.unitIso.symm ≪≫
    Functor.rightUnitor _

/-- The open-site overlap comparison can be pinned to the ambient restriction
triangle. Source: Stacks Project, Tags 08BT and 08BV. Restriction to an open is
a localization, so its precomposition is fully faithful on functor categories.
Descend the pasting of the two site-return maps, the over-site comparison and
the nested scheme restriction comparison. The descent equation is the asserted
triangle and holds also for the empty open. -/
theorem openSiteOverlapIso_exists (X : Scheme.{u}) {W U : X.Opens} (i : W ⟶ U) :
    let PU := (schemeOpenRestriction X U).mapDerivedCategory
    let LU := (overlapSiteInverse U).mapDerivedCategory
    let LW := (overlapSiteInverse W).mapDerivedCategory
    let SP := (SheafOfModules.overMap.{u} (moduleRings X.toRingedSpace) i).mapDerivedCategory
    let SU := (schemeOpenOverlapRestriction X i).mapDerivedCategory
    let RU := (SheafOfModules.overFunctor.{u} (moduleRings X.toRingedSpace) U).mapDerivedCategory
    let RW := (SheafOfModules.overFunctor.{u} (moduleRings X.toRingedSpace) W).mapDerivedCategory
    let siteU := openSiteReturnIso X U
    let siteW := openSiteReturnIso X W
    let τ : RU ⋙ SP ≅ RW := Functor.mapDerivedCategoryCompIso _ _ ≪≫
      Functor.mapDerivedCategoryNatIso
        (SheafOfModules.overFunctorMap.{u} (moduleRings X.toRingedSpace) i)
    let σ := schemeDerivedOpenRestrictionCompIso X i
    ∃ ω : LU ⋙ SP ≅ SU ⋙ LW,
      Functor.isoWhiskerRight siteU SP ≪≫ τ =
        Functor.associator PU LU SP ≪≫
          Functor.isoWhiskerLeft PU ω ≪≫
            (Functor.associator PU SU LW).symm ≪≫
              Functor.isoWhiskerRight σ LW ≪≫ siteW := by
  intro PU LU LW SP SU RU RW siteU siteW τ σ
  let alpha : PU ⋙ (LU ⋙ SP) ≅ PU ⋙ (SU ⋙ LW) :=
    (Functor.associator PU LU SP).symm ≪≫
      Functor.isoWhiskerRight siteU SP ≪≫ τ ≪≫ siteW.symm ≪≫
        Functor.isoWhiskerRight σ.symm LW ≪≫ Functor.associator PU SU LW
  obtain ⟨ω, hω⟩ := Scheme.derived_open_restriction_iso_descent X U
    (LU ⋙ SP) (SU ⋙ LW) alpha
  refine ⟨ω, ?_⟩
  rw [hω]
  dsimp only [alpha]
  apply Iso.ext
  ext K
  have hσ : LW.map (σ.inv.app K) ≫ LW.map (σ.hom.app K) = 𝟙 _ := by
    rw [← LW.map_comp, Iso.inv_hom_id_app, LW.map_id]
  simp only [Iso.trans_hom, Iso.symm_hom, NatTrans.comp_app,
    Functor.isoWhiskerRight_hom, Functor.whiskerRight_app,
    Functor.associator_hom_app, Functor.associator_inv_app,
    Category.assoc, Category.id_comp]
  simpa only [PU, LU, SU, Functor.comp_obj, Category.assoc,
    Iso.app_hom, Iso.app_inv] using
    (cancel_iso_pasting
      (SP.map (siteU.hom.app K) ≫ τ.hom.app K) (siteW.app K)
      (LW.map (σ.inv.app K)) (LW.map (σ.hom.app K)) hσ)

/-- The natural open-site overlap comparison pinned by restriction descent. -/
noncomputable def openSiteOverlapIso (X : Scheme.{u}) {W U : X.Opens} (i : W ⟶ U) :
    (overlapSiteInverse U).mapDerivedCategory ⋙
      (SheafOfModules.overMap.{u} (moduleRings X.toRingedSpace) i).mapDerivedCategory ≅
    (schemeOpenOverlapRestriction X i).mapDerivedCategory ⋙
      (overlapSiteInverse W).mapDerivedCategory :=
  Classical.choose (openSiteOverlapIso_exists X i)

/-- The site-return comparison is coherent with nested open restriction.
Source: Stacks Project, Tags 08BV and 05RU. Both composites insert the same
equivalence unit on the larger open, apply the over-site restriction comparison,
and cancel the smaller-open equivalence by its unit. Exact derivation preserves
these associators and natural isomorphisms. -/
theorem openSiteReturn_overlap_triangle (X : Scheme.{u}) {W U : X.Opens}
    (i : W ⟶ U) :
    let PU := (schemeOpenRestriction X U).mapDerivedCategory
    let _PW := (schemeOpenRestriction X W).mapDerivedCategory
    let LU := (overlapSiteInverse U).mapDerivedCategory
    let LW := (overlapSiteInverse W).mapDerivedCategory
    let SP := (SheafOfModules.overMap.{u} (moduleRings X.toRingedSpace) i).mapDerivedCategory
    let SU := (schemeOpenOverlapRestriction X i).mapDerivedCategory
    let RU := (SheafOfModules.overFunctor.{u} (moduleRings X.toRingedSpace) U).mapDerivedCategory
    let RW := (SheafOfModules.overFunctor.{u} (moduleRings X.toRingedSpace) W).mapDerivedCategory
    let siteU := openSiteReturnIso X U
    let siteW := openSiteReturnIso X W
    let τ : RU ⋙ SP ≅ RW := Functor.mapDerivedCategoryCompIso _ _ ≪≫
      Functor.mapDerivedCategoryNatIso
        (SheafOfModules.overFunctorMap.{u} (moduleRings X.toRingedSpace) i)
    let σ := schemeDerivedOpenRestrictionCompIso X i
    let ω := openSiteOverlapIso X i
    Functor.isoWhiskerRight siteU SP ≪≫ τ =
      Functor.associator PU LU SP ≪≫
        Functor.isoWhiskerLeft PU ω ≪≫
          (Functor.associator PU SU LW).symm ≪≫
            Functor.isoWhiskerRight σ LW ≪≫ siteW := by
  intro PU PW LU LW SP SU RU RW siteU siteW τ σ ω
  exact Classical.choose_spec (openSiteOverlapIso_exists X i)

/-- Component form of the open-site restriction triangle.
Source: Stacks Project, Tags 08BT and 08BV. Evaluate the natural triangle at
the given derived object; its associator components are identities. -/
theorem openSiteReturn_overlap_triangle_app (X : Scheme.{u}) {W U : X.Opens}
    (i : W ⟶ U) (E : schemeDerivedCategory X) :
    let PU := (schemeOpenRestriction X U).mapDerivedCategory
    let LW := (overlapSiteInverse W).mapDerivedCategory
    let SP := (SheafOfModules.overMap.{u} (moduleRings X.toRingedSpace) i).mapDerivedCategory
    let RU := (SheafOfModules.overFunctor.{u} (moduleRings X.toRingedSpace) U).mapDerivedCategory
    let RW := (SheafOfModules.overFunctor.{u} (moduleRings X.toRingedSpace) W).mapDerivedCategory
    let τ : RU ⋙ SP ≅ RW := Functor.mapDerivedCategoryCompIso _ _ ≪≫
      Functor.mapDerivedCategoryNatIso
        (SheafOfModules.overFunctorMap.{u} (moduleRings X.toRingedSpace) i)
    SP.map ((openSiteReturnIso X U).hom.app E) ≫ τ.hom.app E =
      (openSiteOverlapIso X i).hom.app (PU.obj E) ≫
        LW.map ((schemeDerivedOpenRestrictionCompIso X i).hom.app E) ≫
          (openSiteReturnIso X W).hom.app E := by
  intro PU LW SP RU RW τ
  have h := congrArg (fun e ↦ e.hom.app E) (openSiteReturn_overlap_triangle X i)
  simpa only [PU, LW, SP, RU, RW, τ, Iso.trans_hom, NatTrans.comp_app,
    Functor.isoWhiskerRight_hom,
    Functor.isoWhiskerLeft_hom, Functor.whiskerRight_app,
    Functor.whiskerLeft_app, Functor.associator_hom_app,
    Functor.associator_inv_app, Iso.symm_hom,
    Functor.comp_obj, Category.id_comp, Category.assoc] using h

/-- Inverse component of the open-site restriction triangle. Invert the
isomorphism equality from `openSiteReturn_overlap_triangle_app`, then cancel
the return comparison at the smaller open. -/
theorem openSiteReturn_overlap_triangle_inv_app (X : Scheme.{u}) {W U : X.Opens}
    (i : W ⟶ U) (E : schemeDerivedCategory X) :
    let PU := (schemeOpenRestriction X U).mapDerivedCategory
    let LW := (overlapSiteInverse W).mapDerivedCategory
    let SP := (SheafOfModules.overMap.{u} (moduleRings X.toRingedSpace) i).mapDerivedCategory
    let RU := (SheafOfModules.overFunctor.{u} (moduleRings X.toRingedSpace) U).mapDerivedCategory
    let RW := (SheafOfModules.overFunctor.{u} (moduleRings X.toRingedSpace) W).mapDerivedCategory
    let τ : RU ⋙ SP ≅ RW := Functor.mapDerivedCategoryCompIso _ _ ≪≫
      Functor.mapDerivedCategoryNatIso
        (SheafOfModules.overFunctorMap.{u} (moduleRings X.toRingedSpace) i)
    let σ := schemeDerivedOpenRestrictionCompIso X i
    let ω := openSiteOverlapIso X i
    (openSiteReturnIso X W).hom.app E ≫ τ.inv.app E ≫
      SP.map ((openSiteReturnIso X U).inv.app E) =
        LW.map (σ.inv.app E) ≫ ω.inv.app (PU.obj E) := by
  intro PU LW SP RU RW τ σ ω
  let a := SP.mapIso ((openSiteReturnIso X U).app E)
  let b := τ.app E
  let c := ω.app (PU.obj E)
  let d := LW.mapIso (σ.app E)
  let e := (openSiteReturnIso X W).app E
  have hf : a.hom ≫ b.hom = c.hom ≫ d.hom ≫ e.hom := by
    simpa only [a, b, c, d, e, Functor.mapIso_hom, Iso.app_hom] using
      openSiteReturn_overlap_triangle_app X i E
  have hc : e.hom ≫ b.inv ≫ a.inv = d.inv ≫ c.inv :=
    iso_triangle_inverse_cancel a b c d e hf
  simpa only [a, b, c, d, e, Functor.mapIso_inv, Iso.app_hom, Iso.app_inv]
    using hc

/-- Naturality of the open-site overlap comparison cancels an inverse and
forward component around any local morphism. -/
theorem openSiteOverlap_inv_map_hom (X : Scheme.{u}) {W U : X.Opens}
    (i : W ⟶ U) {M N : schemeDerivedCategory U.toScheme} (t : M ⟶ N) :
    let LU := (overlapSiteInverse U).mapDerivedCategory
    let LW := (overlapSiteInverse W).mapDerivedCategory
    let SP := (SheafOfModules.overMap.{u} (moduleRings X.toRingedSpace) i).mapDerivedCategory
    let SU := (schemeOpenOverlapRestriction X i).mapDerivedCategory
    (openSiteOverlapIso X i).inv.app M ≫ SP.map (LU.map t) ≫
        (openSiteOverlapIso X i).hom.app N = LW.map (SU.map t) := by
  intro LU LW SP SU
  simpa only [Functor.comp_map] using
    (NatIso.naturality_1 (openSiteOverlapIso X i) t)



/-- The two paths around an open-restriction square agree by pullback composition.
Use the fixed composition comparisons and the constructed open-pullback comparisons. -/
noncomputable def openPullbackRestrictionIso
    {X Y : Scheme.{u}} (g : X ⟶ Y) (P : X.Opens) (U : Y.Opens)
    (h : P ≤ g ⁻¹ᵁ U) :
    derivedPullback g ⋙ (schemeOpenRestriction X P).mapDerivedCategory ≅
      (schemeOpenRestriction Y U).mapDerivedCategory ⋙ derivedPullback (g.resLE U P h) :=
  Functor.isoWhiskerLeft _ (singleComplexOpenPullbackIso X P).symm ≪≫
    perfectHomComposition P.ι g ≪≫
    eqToIso (congrArg (fun f ↦ derivedPullback f) (g.resLE_comp_ι h).symm) ≪≫
    (perfectHomComposition (g.resLE U P h) U.ι).symm ≪≫
    Functor.isoWhiskerRight (singleComplexOpenPullbackIso Y U) _

/-- A global object whose pullback restricts to the pullback of an open object.
The global precursor exists because derived restriction to an open is a
localization and hence essentially surjective. -/
noncomputable def perfectOverlapOpenLiftObject
    {X Y : Scheme.{u}} (f : X ⟶ Y) (U : Y.Opens)
    (A : schemeDerivedCategory U.toScheme) : schemeDerivedCategory X := by
  let rY := (schemeOpenRestriction Y U).mapDerivedCategory
  let W := (MorphismProperty.isomorphisms _).inverseImage rY
  letI : rY.IsLocalization W := schemeDerivedOpenRestriction_isLocalization Y U
  letI : rY.EssSurj := Localization.essSurj rY W
  exact (derivedPullback f).obj (rY.objPreimage A)

/-- The chosen global lift restricts to the pulled-back open object.
Source: Stacks Project, Tag 08DW. Choose the localization preimage of the
original open object. The open-pullback square identifies restriction after
pullback with pullback after restriction; map the preimage isomorphism through
the restricted pullback functor. Their composite gives the displayed iso. -/
noncomputable def perfectOverlapOpenLiftIso
    {X Y : Scheme.{u}} (f : X ⟶ Y) (U : Y.Opens)
    (A : schemeDerivedCategory U.toScheme) :
    (schemeOpenRestriction X (f ⁻¹ᵁ U)).mapDerivedCategory.obj
        (perfectOverlapOpenLiftObject f U A) ≅
      (derivedPullback (f ∣_ U)).obj A := by
  let rY := (schemeOpenRestriction Y U).mapDerivedCategory
  let W := (MorphismProperty.isomorphisms _).inverseImage rY
  letI : rY.IsLocalization W := schemeDerivedOpenRestriction_isLocalization Y U
  letI : rY.EssSurj := Localization.essSurj rY W
  let M := rY.objPreimage A
  let e := rY.objObjPreimageIso A
  change ((schemeOpenRestriction X (f ⁻¹ᵁ U)).mapDerivedCategory.obj
    ((derivedPullback f).obj M)) ≅ (derivedPullback (f ∣_ U)).obj A
  have β' :
      (schemeOpenRestriction X (f ⁻¹ᵁ U)).mapDerivedCategory.obj
          ((derivedPullback f).obj M) ≅
        (derivedPullback (f ∣_ U)).obj (rY.obj M) := by
    exact (singleComplexOpenPullbackSquareIso f U (f ⁻¹ᵁ U) (f ∣_ U)
      (morphismRestrict_ι f U)).symm.app M
  exact β' ≪≫ (derivedPullback (f ∣_ U)).mapIso e

/-- The fixed restriction/pullback comparison on one open. Its implementation
contains the derived open-site return, associator, and cartesian pullback
comparison; keeping this composition named avoids unfolding it while
constructing and comparing the three overlap diagram components. -/
@[irreducible] noncomputable def perfectOverlapRestrictionBeta
    {X Y : Scheme.{u}} (g : X ⟶ Y) (W : Y.Opens) (T : X.Opens)
    (hT : T ≤ g ⁻¹ᵁ W) :
    derivedPullback g ⋙
        (SheafOfModules.overFunctor.{u} (moduleRings X.toRingedSpace) T).mapDerivedCategory ≅
      (schemeOpenRestriction Y W).mapDerivedCategory ⋙
        (derivedPullback (g.resLE W T hT) ⋙ (overlapSiteInverse T).mapDerivedCategory) :=
  Functor.isoWhiskerLeft _ (openSiteReturnIso X T).symm ≪≫
    (Functor.associator _ _ _).symm ≪≫
      Functor.isoWhiskerRight (openPullbackRestrictionIso g T W hT) _ ≪≫
      Functor.associator _ _ _

/-- Component equation for the named restriction/pullback comparison.
Source: Stacks Project, Tags 08DW and 08BV. The two associators have identity
components, so the comparison first returns from the over-site and then
applies the cartesian open-pullback comparison under the inverse site functor. -/
theorem perfectOverlapRestrictionBeta_hom_app
    {X Y : Scheme.{u}} (g : X ⟶ Y) (W : Y.Opens) (T : X.Opens)
    (hT : T ≤ g ⁻¹ᵁ W) (E : schemeDerivedCategory Y) :
    (perfectOverlapRestrictionBeta g W T hT).hom.app E =
      (openSiteReturnIso X T).inv.app ((derivedPullback g).obj E) ≫
        (overlapSiteInverse T).mapDerivedCategory.map
          ((openPullbackRestrictionIso g T W hT).hom.app E) := by
  unfold perfectOverlapRestrictionBeta
  simp only [Iso.trans_hom, NatTrans.comp_app, Iso.symm_hom,
    Functor.isoWhiskerLeft_hom, Functor.isoWhiskerRight_hom,
    Functor.whiskerLeft_app, Functor.whiskerRight_app,
    Functor.associator_hom_app, Functor.associator_inv_app,
    Category.id_comp, Category.comp_id]

/-- Inverse component of the restriction/pullback comparison. The two
associators have identity components; the inverse open-pullback comparison
is followed by the open-site return map. -/
theorem perfectOverlapRestrictionBeta_inv_app
    {X Y : Scheme.{u}} (g : X ⟶ Y) (W : Y.Opens) (T : X.Opens)
    (hT : T ≤ g ⁻¹ᵁ W) (E : schemeDerivedCategory Y) :
    (perfectOverlapRestrictionBeta g W T hT).inv.app E =
      (overlapSiteInverse T).mapDerivedCategory.map
        ((openPullbackRestrictionIso g T W hT).inv.app E) ≫
          (openSiteReturnIso X T).hom.app ((derivedPullback g).obj E) := by
  unfold perfectOverlapRestrictionBeta
  simp only [Iso.trans_inv, NatTrans.comp_app, Iso.symm_inv,
    Functor.isoWhiskerLeft_inv, Functor.isoWhiskerRight_inv,
    Functor.whiskerLeft_app, Functor.whiskerRight_app,
    Functor.associator_hom_app, Functor.associator_inv_app,
    Category.id_comp, Category.comp_id]

end

end AlgebraicGeometry

