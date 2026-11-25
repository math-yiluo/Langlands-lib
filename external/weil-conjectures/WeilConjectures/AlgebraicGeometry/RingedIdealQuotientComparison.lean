/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.Abelian
public import WeilConjectures.AlgebraicGeometry.RingedSiteIdeal
public import WeilConjectures.AlgebraicGeometry.RingedTopoiTensorSections
import Mathlib.Algebra.Category.Grp.Abelian
import Mathlib.Algebra.Category.Grp.EpiMono
import Mathlib.CategoryTheory.Adjunction.Additive
import Mathlib.CategoryTheory.Sites.Abelian
import Mathlib.CategoryTheory.Sites.EpiMono
import Mathlib.RingTheory.Ideal.Quotient.Operations
import WeilConjectures.AlgebraicGeometry.ExtendedLocalizationCech
import WeilConjectures.Mathlib.Algebra.Category.ModuleCat.Presheaf.Sheafification

/-! # The quotient criterion for an ideal subsheaf

Source: Stacks Project, Modules on Sites, Tags 03D7 and 03CY; Algebraization, Tag 099I.
(auxiliary; not a blueprint node).
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory CategoryTheory.Limits Opposite
namespace CategoryTheory.RingedSiteIdeal
variable {C : Type u} [SmallCategory C] {J : GrothendieckTopology C}
  {R B : Sheaf J CommRingCat.{u}}

attribute [local irreducible] SheafOfModules.RingedTensor.tensorAdjunction
  SheafOfModules.RingedTensor.tensorFunctor

/-- Restriction on sectionwise ideal quotients.
Source: Stacks Project, Modules on Sites, Tag 03D7; Algebraization, Tag 099I.
(auxiliary; not a blueprint node). -/
private def quotientMap (I : RingedSiteIdeal R) {X Y : Cᵒᵖ} (f : X ⟶ Y) :
    ModuleCat.of (R.obj.obj X) (R.obj.obj X ⧸ I.sections X.unop) ⟶
      (ModuleCat.restrictScalars ((siteModuleRings R).obj.map f).hom).obj
        (ModuleCat.of (R.obj.obj Y) (R.obj.obj Y ⧸ I.sections Y.unop)) := by
  let g : R.obj.obj X →ₛₗ[(R.obj.map f).hom] R.obj.obj Y :=
    { toFun := R.obj.map f
      map_add' := map_add (R.obj.map f).hom
      map_smul' := fun a b ↦ map_mul (R.obj.map f).hom a b }
  let q := (I.sections X.unop).mapQ (I.sections Y.unop) g
    (fun a ha ↦ I.restriction f.unop a ha)
  exact ModuleCat.ofHom
    (X := ModuleCat.of (R.obj.obj X) (R.obj.obj X ⧸ I.sections X.unop))
    (Y := (ModuleCat.restrictScalars ((siteModuleRings R).obj.map f).hom).obj
      (ModuleCat.of (R.obj.obj Y) (R.obj.obj Y ⧸ I.sections Y.unop)))
    { toFun := q
      map_add' := q.map_add
      map_smul' := fun a b ↦ q.map_smulₛₗ a b }

private theorem quotientMap_mk (I : RingedSiteIdeal R) {X Y : Cᵒᵖ} (f : X ⟶ Y)
    (a : R.obj.obj X) :
    quotientMap I f (Submodule.Quotient.mk a) =
      Submodule.Quotient.mk (R.obj.map f a) := rfl

/-- The sectionwise quotient module presheaf of an ideal subsheaf.
Source: Stacks Project, Modules on Sites, Tag 03D7; Algebraization, Tag 099I.
(auxiliary; not a blueprint node). -/
private def quotientPresheaf (I : RingedSiteIdeal R) :
    PresheafOfModules.{u} (siteModuleRings R).obj where
  obj X := ModuleCat.of (R.obj.obj X) (R.obj.obj X ⧸ I.sections X.unop)
  map f := quotientMap I f
  map_id X := by
    apply ModuleCat.hom_ext
    apply LinearMap.ext
    intro a
    induction a using Submodule.Quotient.induction_on with
    | _ a =>
      rw [quotientMap_mk]
      exact congrArg Submodule.Quotient.mk (congrArg (fun g ↦ g a) (R.obj.map_id X))
  map_comp f g := by
    apply ModuleCat.hom_ext
    apply LinearMap.ext
    intro a
    induction a using Submodule.Quotient.induction_on with
    | _ a =>
      change quotientMap I (f ≫ g) (Submodule.Quotient.mk a) =
        quotientMap I g (quotientMap I f (Submodule.Quotient.mk a))
      dsimp only [quotientMap_mk]
      exact congrArg (Submodule.Quotient.mk (p := I.sections _))
        (congrArg (fun h ↦ h a) (R.obj.map_comp f g))

private def quotientProjection (I : RingedSiteIdeal R) :
    (SheafOfModules.unit (siteModuleRings R)).val ⟶ quotientPresheaf I where
  app X := ModuleCat.ofHom (R := R.obj.obj X)
    (X := ModuleCat.of (R.obj.obj X) (R.obj.obj X))
    (Y := ModuleCat.of (R.obj.obj X) (R.obj.obj X ⧸ I.sections X.unop))
    (I.sections X.unop).mkQ
  naturality f := by
    apply ModuleCat.hom_ext
    apply LinearMap.ext
    intro a
    rfl

/-- An ideal section maps into the extended ideal.
Source: Stacks Project, Modules on Sites, Tag 03D7; Algebraization, Tag 099I.
(auxiliary; not a blueprint node). -/
private theorem extension_mem (I : RingedSiteIdeal R) (φ : R ⟶ B)
    (U : C) (a : I.sections U) :
    φ.hom.app (op U) a ∈ (I.extension φ).sections U := by
  apply ((Classical.choose_spec (existsUnique_extension I φ).exists) U _).mpr
  refine ⟨⊤, J.top_mem _, ?_⟩
  intro V g _
  have hnat := congrArg (fun h ↦ h a.val) (φ.hom.naturality g.op)
  change φ.hom.app (op V) (R.obj.map g.op a.val) =
    B.obj.map g.op (φ.hom.app (op U) a.val) at hnat
  rw [← hnat]
  exact Ideal.subset_span ⟨⟨R.obj.map g.op a.val, I.restriction g a.val a.property⟩, rfl⟩

/-- The map of additive section quotients induced by a ring map.
Source: Stacks Project, Modules on Sites, Tag 03D7; Algebraization, Tag 099I.
(auxiliary; not a blueprint node). -/
private def quotientCoefficientMap (I : RingedSiteIdeal R) (φ : R ⟶ B) (X : Cᵒᵖ) :
    AddCommGrpCat.of (R.obj.obj X ⧸ I.sections X.unop) ⟶
      AddCommGrpCat.of (B.obj.obj X ⧸ (I.extension φ).sections X.unop) := by
  let g := Ideal.quotientMap ((I.extension φ).sections X.unop) (φ.hom.app X).hom
    (fun a ha ↦ extension_mem I φ X.unop ⟨a, ha⟩)
  exact AddCommGrpCat.ofHom g.toAddMonoidHom

/-- The canonical map of additive quotient presheaves.
Source: Stacks Project, Modules on Sites, Tag 03D7; Algebraization, Tag 099I.
(auxiliary; not a blueprint node). -/
private def quotientComparison (I : RingedSiteIdeal R) (φ : R ⟶ B) :
    (quotientPresheaf I).presheaf ⟶ (quotientPresheaf (I.extension φ)).presheaf where
  app X := quotientCoefficientMap I φ X
  naturality {X Y} g := by
    apply AddCommGrpCat.hom_ext
    ext a
    induction a using Submodule.Quotient.induction_on with
    | _ a =>
      change (Submodule.Quotient.mk (φ.hom.app Y (R.obj.map g a)) :
        B.obj.obj Y ⧸ (I.extension φ).sections Y.unop) =
        Submodule.Quotient.mk (B.obj.map g (φ.hom.app X a))
      exact congrArg (Submodule.Quotient.mk (p := (I.extension φ).sections Y.unop))
        (congrArg (fun h ↦ h a) (φ.hom.naturality g))

private theorem quotientComparison_injective (I : RingedSiteIdeal R) (φ : R ⟶ B)
    (hquot : I.IsQuotientIso φ) (X : Cᵒᵖ) :
    Function.Injective ((quotientComparison I φ).app X) := by
  intro a b h
  induction a using Submodule.Quotient.induction_on with
  | _ a =>
    induction b using Submodule.Quotient.induction_on with
    | _ b =>
      apply (Submodule.Quotient.eq _).mpr
      apply (hquot.1 X.unop (a - b)).mp
      rw [map_sub]
      exact (Submodule.Quotient.eq _).mp h

private theorem quotientComparison_locallySurjective (I : RingedSiteIdeal R) (φ : R ⟶ B)
    (hquot : I.IsQuotientIso φ) :
    Presheaf.IsLocallySurjective J (quotientComparison I φ) := by
  constructor
  intro U b
  induction b using Submodule.Quotient.induction_on with
  | _ b =>
    obtain ⟨S, hS, h⟩ := hquot.2 U b
    apply J.superset_covering (S := S) ?_ hS
    intro V g hg
    obtain ⟨a, ha⟩ := h V g hg
    refine ⟨Submodule.Quotient.mk a, ?_⟩
    apply (Submodule.Quotient.eq _).mpr
    change φ.hom.app (op V) a - B.obj.map g.op b ∈ (I.extension φ).sections V
    simpa only [neg_sub] using (I.extension φ).sections V |>.neg_mem ha

/-- The local quotient criterion makes the canonical quotient comparison an isomorphism
following sheafification.
Source: Stacks Project, Modules on Sites, Tags 03D7 and 03CY; Algebraization, Tag 099I.
(auxiliary; not a blueprint node).

Proof: the local kernel criterion gives injectivity on section quotients. The local lifting
criterion gives a covering sieve of preimages of every quotient section. A locally bijective
map of presheaves becomes an isomorphism after sheafification. No claim that sectionwise
quotients already form a sheaf is needed.
-/
private theorem quotientComparison_sheafification_isIso (I : RingedSiteIdeal R) (φ : R ⟶ B)
    (hquot : I.IsQuotientIso φ) :
    IsIso ((presheafToSheaf J AddCommGrpCat).map (quotientComparison I φ)) := by
  have := Presheaf.isLocallyInjective_of_injective J (quotientComparison I φ)
    (quotientComparison_injective I φ hquot)
  have := quotientComparison_locallySurjective I φ hquot
  exact (J.W_iff _).mp (J.W_of_isLocallyBijective _)

private theorem quotientProjection_zero (I : RingedSiteIdeal R) :
    I.inclusion.val ≫ quotientProjection I = 0 := by
  apply PresheafOfModules.hom_ext
  intro X
  apply ModuleCat.hom_ext
  apply LinearMap.ext
  intro a
  exact (Submodule.Quotient.mk_eq_zero _).mpr a.property

private noncomputable def quotientPresheafIsCokernel (I : RingedSiteIdeal R) :
    IsColimit (CokernelCofork.ofπ (quotientProjection I) (quotientProjection_zero I)) := by
  apply PresheafOfModules.evaluationJointlyReflectsColimits
  intro X
  refine (CokernelCofork.isColimitMapCoconeEquiv _
    (PresheafOfModules.evaluation (siteModuleRings R).obj X)).symm ?_
  apply ModuleCat.isColimitCokernelCofork
  · intro a
    constructor
    · intro ha
      refine ⟨⟨a, ?_⟩, rfl⟩
      exact (Submodule.Quotient.mk_eq_zero _).mp ha
    · rintro ⟨b, rfl⟩
      exact (Submodule.Quotient.mk_eq_zero _).mpr b.property
  · exact Submodule.mkQ_surjective _

private noncomputable def idealCoefficientMap (I : RingedSiteIdeal R) (φ : R ⟶ B) :
    I.module ⟶ (SheafOfModules.RingedTensor.restriction φ).obj (I.extension φ).module where
  val :=
    { app := fun X ↦ ModuleCat.ofHom
        (X := I.module.val.obj X)
        (Y := ((SheafOfModules.RingedTensor.restriction φ).obj
          (I.extension φ).module).val.obj X)
        { toFun := fun a ↦ ⟨φ.hom.app X a.val, extension_mem I φ X.unop a⟩
          map_add' := fun a b ↦ Subtype.ext (map_add (φ.hom.app X).hom a.val b.val)
          map_smul' := fun a b ↦ Subtype.ext (map_mul (φ.hom.app X).hom a b.val) }
      naturality {X Y} g := by
        apply ModuleCat.hom_ext
        apply LinearMap.ext
        intro a
        apply Subtype.ext
        exact congrArg (fun h ↦ h a.val) (φ.hom.naturality g) }

private noncomputable def extendedIdealMap (I : RingedSiteIdeal R) (φ : R ⟶ B) :
    (SheafOfModules.RingedTensor.tensorFunctor φ).obj I.module ⟶
      (I.extension φ).module :=
  ((SheafOfModules.RingedTensor.tensorAdjunction φ).homEquiv _ _).symm
    (idealCoefficientMap I φ)

private theorem extendedIdealMap_unit (I : RingedSiteIdeal R) (φ : R ⟶ B)
    (X : Cᵒᵖ) (a : I.sections X.unop) :
    (extendedIdealMap I φ).val.app X
      (((SheafOfModules.RingedTensor.tensorAdjunction φ).unit.app I.module).val.app X a) =
        ⟨φ.hom.app X a.val, extension_mem I φ X.unop a⟩ := by
  have h := ((SheafOfModules.RingedTensor.tensorAdjunction φ).homEquiv _ _).apply_symm_apply
    (idealCoefficientMap I φ)
  rw [Adjunction.homEquiv_unit] at h
  exact congrArg (fun k ↦ k.val.app X a) h

private theorem extendedIdealMap_epi (I : RingedSiteIdeal R) (φ : R ⟶ B) :
    Epi (extendedIdealMap I φ) := by
  let p := extendedIdealMap I φ
  let V := SheafOfModules.toSheaf (siteModuleRings B)
  suffices h : Epi (V.map p) from V.epi_of_epi_map h
  apply (Sheaf.isLocallySurjective_iff_epi' _ _).mp
  constructor
  intro U b
  obtain ⟨S, hS, hb⟩ :=
    ((Classical.choose_spec (existsUnique_extension I φ).exists) U b.val).mp b.property
  apply J.superset_covering (S := S) ?_ hS
  intro W g hg
  have hx := hb W g hg
  have lift (x : B.obj.obj (op W))
      (hx : x ∈ Ideal.span (Set.range (fun a : I.sections W ↦ φ.hom.app (op W) a.val))) :
      ∃ t : ((SheafOfModules.RingedTensor.tensorFunctor φ).obj I.module).val.obj (op W),
        ((p.val.app (op W)) t).val = x := by
    induction hx using Submodule.span_induction with
    | mem x hx =>
      obtain ⟨a, rfl⟩ := hx
      exact ⟨((SheafOfModules.RingedTensor.tensorAdjunction φ).unit.app I.module).val.app
        (op W) a, congrArg Subtype.val (extendedIdealMap_unit I φ (op W) a)⟩
    | zero => exact ⟨0, by simp⟩
    | add x y hx hy hxl hyl =>
      obtain ⟨a, ha⟩ := hxl
      obtain ⟨b, hb⟩ := hyl
      refine ⟨a + b, ?_⟩
      rw [map_add]
      change ((p.val.app (op W)) a).val + ((p.val.app (op W)) b).val = _
      rw [ha, hb]
    | smul a x hx hxl =>
      obtain ⟨b, hb⟩ := hxl
      refine ⟨a • b, ?_⟩
      rw [map_smul]
      change a * ((p.val.app (op W)) b).val = _
      rw [hb]
      rfl
  obtain ⟨a, ha⟩ := lift _ hx
  exact ⟨a, Subtype.ext ha⟩

@[irreducible] private noncomputable def additiveQuotientCokernelData
    (I : RingedSiteIdeal R) :
    { e : (presheafToSheaf J AddCommGrpCat).obj (quotientPresheaf I).presheaf ≅
      (SheafOfModules.toSheaf (siteModuleRings R)).obj (cokernel I.inclusion) //
    (presheafToSheaf J AddCommGrpCat).map
        ((PresheafOfModules.toPresheaf _).map (quotientProjection I)) ≫ e.hom =
    (sheafificationAdjunction J AddCommGrpCat).counit.app
        ((SheafOfModules.toSheaf (siteModuleRings R)).obj
          (SheafOfModules.unit (siteModuleRings R))) ≫
      (SheafOfModules.toSheaf (siteModuleRings R)).map
        (cokernel.π I.inclusion) } := by
  let V := SheafOfModules.toSheaf (siteModuleRings R)
  let T := PresheafOfModules.toPresheaf (siteModuleRings R).obj
  let S := presheafToSheaf J AddCommGrpCat.{u}
  let c := CokernelCofork.ofπ (quotientProjection I) (quotientProjection_zero I)
  let hc := CokernelCofork.mapIsColimit (c.map T)
    (CokernelCofork.mapIsColimit c (quotientPresheafIsCokernel I) T) S
  let d := (CokernelCofork.ofπ (cokernel.π I.inclusion) (cokernel.condition _)).map V
  let hd := CokernelCofork.mapIsColimit _ (cokernelIsCokernel I.inclusion) V
  let ε := (sheafificationAdjunction J AddCommGrpCat.{u}).counit
  let a : Arrow.mk (S.map (T.map I.inclusion.val)) ≅ Arrow.mk (V.map I.inclusion) :=
    Arrow.isoMk (asIso (ε.app (V.obj I.module)))
      (asIso (ε.app (V.obj (SheafOfModules.unit (siteModuleRings R)))))
      (by exact (ε.naturality (V.map I.inclusion)).symm)
  refine ⟨CokernelCofork.mapIsoOfIsColimit (cc' := d) hc hd a, ?_⟩
  exact CokernelCofork.π_mapOfIsColimit hc d a.hom

private noncomputable def additiveQuotientCokernelIso (I : RingedSiteIdeal R) :=
  (additiveQuotientCokernelData I).val

private theorem additiveQuotientCokernelIso_π (I : RingedSiteIdeal R) :
    (presheafToSheaf J AddCommGrpCat).map
        ((PresheafOfModules.toPresheaf _).map (quotientProjection I)) ≫
      (additiveQuotientCokernelIso I).hom =
    (sheafificationAdjunction J AddCommGrpCat).counit.app
        ((SheafOfModules.toSheaf (siteModuleRings R)).obj
          (SheafOfModules.unit (siteModuleRings R))) ≫
      (SheafOfModules.toSheaf (siteModuleRings R)).map (cokernel.π I.inclusion) :=
  (additiveQuotientCokernelData I).property

private theorem idealCoefficientMap_inclusion (I : RingedSiteIdeal R) (φ : R ⟶ B) :
    I.inclusion ≫ SheafOfModules.LocalizationCech.unitMap φ =
      idealCoefficientMap I φ ≫ (SheafOfModules.RingedTensor.restriction φ).map
        (I.extension φ).inclusion := by
  apply SheafOfModules.hom_ext
  apply PresheafOfModules.hom_ext
  intro X
  apply ModuleCat.hom_ext
  apply LinearMap.ext
  intro a
  exact (SheafOfModules.LocalizationCech.unitMap_existsUnique φ).choose_spec.1 X a.val

private noncomputable def cokernelCoefficientMap (I : RingedSiteIdeal R) (φ : R ⟶ B) :
    cokernel I.inclusion ⟶ (SheafOfModules.RingedTensor.restriction φ).obj
      (cokernel (I.extension φ).inclusion) :=
  cokernel.desc I.inclusion
    (SheafOfModules.LocalizationCech.unitMap φ ≫
      (SheafOfModules.RingedTensor.restriction φ).map
        (cokernel.π (I.extension φ).inclusion)) (by
    rw [← Category.assoc, idealCoefficientMap_inclusion, Category.assoc, ← Functor.map_comp,
      cokernel.condition, Functor.map_zero, comp_zero])

private theorem quotientProjection_coefficient (I : RingedSiteIdeal R) (φ : R ⟶ B) :
    (PresheafOfModules.toPresheaf _).map (quotientProjection I) ≫ quotientComparison I φ =
      ((SheafOfModules.toSheaf (siteModuleRings R)).map
        (SheafOfModules.LocalizationCech.unitMap φ)).hom ≫
      (PresheafOfModules.toPresheaf (siteModuleRings B).obj).map
        (quotientProjection (I.extension φ)) := by
  apply NatTrans.ext
  funext X
  apply AddCommGrpCat.hom_ext
  ext a
  change R.obj.obj X at a
  change (Submodule.Quotient.mk (φ.hom.app X a) :
      B.obj.obj X ⧸ (I.extension φ).sections X.unop) =
    Submodule.Quotient.mk (p := (I.extension φ).sections X.unop)
      (show B.obj.obj X from
        (SheafOfModules.LocalizationCech.unitMap φ).val.app X a)
  exact congrArg (Submodule.Quotient.mk (p := (I.extension φ).sections X.unop))
    ((SheafOfModules.LocalizationCech.unitMap_existsUnique φ).choose_spec.1 X a).symm

private theorem cokernelCoefficientMap_isIso (I : RingedSiteIdeal R) (φ : R ⟶ B)
    (hquot : I.IsQuotientIso φ) : IsIso (cokernelCoefficientMap I φ) := by
  let V := SheafOfModules.toSheaf (siteModuleRings R)
  let W := SheafOfModules.toSheaf (siteModuleRings B)
  let S := presheafToSheaf J AddCommGrpCat.{u}
  let p := (PresheafOfModules.toPresheaf _).map (quotientProjection I)
  let q := (PresheafOfModules.toPresheaf _).map (quotientProjection (I.extension φ))
  let v := V.map (SheafOfModules.LocalizationCech.unitMap φ)
  let e := additiveQuotientCokernelIso I
  let e' := additiveQuotientCokernelIso (I.extension φ)
  have he : S.map p ≫ e.hom =
      (sheafificationAdjunction J AddCommGrpCat).counit.app _ ≫ V.map (cokernel.π I.inclusion) :=
    additiveQuotientCokernelIso_π I
  have he' : S.map q ≫ e'.hom =
      (sheafificationAdjunction J AddCommGrpCat).counit.app _ ≫
        W.map (cokernel.π (I.extension φ).inclusion) :=
    additiveQuotientCokernelIso_π (I.extension φ)
  have : Epi (S.map p ≫ e.hom) := by rw [he]; infer_instance
  have : Epi (S.map p) := by
    have := epi_comp (S.map p ≫ e.hom) e.inv
    simpa only [Category.assoc, Iso.hom_inv_id, Category.comp_id] using this
  have hc : e.hom ≫ V.map (cokernelCoefficientMap I φ) =
      S.map (quotientComparison I φ) ≫ e'.hom := by
    apply (cancel_epi (S.map p)).mp
    rw [← Category.assoc, he, Category.assoc, ← V.map_comp,
      cokernelCoefficientMap, cokernel.π_desc, V.map_comp]
    have hqp : p ≫ quotientComparison I φ = v.hom ≫ q :=
      quotientProjection_coefficient I φ
    have hmap := congrArg S.map hqp
    simp only [S.map_comp] at hmap
    conv_rhs => rw [← Category.assoc, hmap, Category.assoc, he']
    change (_ ≫ v) ≫ W.map (cokernel.π (I.extension φ).inclusion) =
      S.map v.hom ≫ _ ≫ W.map (cokernel.π (I.extension φ).inclusion)
    rw [← Category.assoc]
    exact congrArg (fun a ↦ a ≫ W.map (cokernel.π (I.extension φ).inclusion))
      ((sheafificationAdjunction J AddCommGrpCat).counit.naturality v).symm
  have := quotientComparison_sheafification_isIso I φ hquot
  have : IsIso (e.hom ≫ V.map (cokernelCoefficientMap I φ)) := by rw [hc]; infer_instance
  have : IsIso (V.map (cokernelCoefficientMap I φ)) :=
    IsIso.of_isIso_comp_left e.hom _
  exact isIso_of_reflects_iso _ V

private noncomputable def scalarRingMap (φ : R ⟶ B) :
    (SheafOfModules.RingedTensor.tensorFunctor φ).obj
      (SheafOfModules.unit (siteModuleRings R)) ⟶ SheafOfModules.unit (siteModuleRings B) :=
  ((SheafOfModules.RingedTensor.tensorAdjunction φ).homEquiv _ _).symm
    (SheafOfModules.LocalizationCech.unitMap φ)

private theorem scalarRingMap_unit (φ : R ⟶ B) :
    (SheafOfModules.RingedTensor.tensorAdjunction φ).unit.app
        (SheafOfModules.unit (siteModuleRings R)) ≫
      (SheafOfModules.RingedTensor.restriction φ).map (scalarRingMap φ) =
        SheafOfModules.LocalizationCech.unitMap φ := by
  exact ((SheafOfModules.RingedTensor.tensorAdjunction φ).homEquiv _ _).apply_symm_apply _

private noncomputable def scalarRingInverse (φ : R ⟶ B) :
    SheafOfModules.unit (siteModuleRings B) ⟶
      (SheafOfModules.RingedTensor.tensorFunctor φ).obj
        (SheafOfModules.unit (siteModuleRings R)) := by
  let η := (SheafOfModules.RingedTensor.tensorAdjunction φ).unit.app
    (SheafOfModules.unit (siteModuleRings R))
  exact ((SheafOfModules.RingedTensor.tensorFunctor φ).obj
    (SheafOfModules.unit (siteModuleRings R))).unitHomEquiv.symm
    (PresheafOfModules.sectionsMk (fun X ↦ η.val.app X (1 : R.obj.obj X)) (by
      intro X Y f
      have h := PresheafOfModules.naturality_apply η.val f (1 : R.obj.obj X)
      change η.val.app Y (R.obj.map f (1 : R.obj.obj X)) = _ at h
      rw [map_one] at h
      exact h.symm))

private theorem scalarRingInverse_apply (φ : R ⟶ B) (X : Cᵒᵖ) :
    (scalarRingInverse φ).val.app X (1 : B.obj.obj X) =
      ((SheafOfModules.RingedTensor.tensorAdjunction φ).unit.app
        (SheafOfModules.unit (siteModuleRings R))).val.app X (1 : R.obj.obj X) := by
  let z : ((SheafOfModules.RingedTensor.tensorFunctor φ).obj
      (SheafOfModules.unit (siteModuleRings R))).val.obj X :=
    ((SheafOfModules.RingedTensor.tensorAdjunction φ).unit.app
      (SheafOfModules.unit (siteModuleRings R))).val.app X (1 : R.obj.obj X)
  change (1 : B.obj.obj X) • z = z
  exact one_smul _ _

private theorem scalarRingMap_isIso (φ : R ⟶ B) : IsIso (scalarRingMap φ) := by
  let adj := SheafOfModules.RingedTensor.tensorAdjunction φ
  let A := SheafOfModules.unit (siteModuleRings R)
  let D := SheafOfModules.unit (siteModuleRings B)
  let μ := scalarRingMap φ
  let ν := scalarRingInverse φ
  have hνμ : ν ≫ μ = 𝟙 D := by
    apply D.unitHomEquiv.injective
    apply Subtype.ext
    funext X
    change μ.val.app X (ν.val.app X (1 : B.obj.obj X)) = (1 : B.obj.obj X)
    rw [scalarRingInverse_apply]
    have h := congrArg (fun k ↦ k.val.app X (1 : R.obj.obj X)) (scalarRingMap_unit φ)
    exact h.trans (((SheafOfModules.LocalizationCech.unitMap_existsUnique φ).choose_spec.1
      X (1 : R.obj.obj X)).trans (φ.hom.app X).hom.map_one)
  have hμν : μ ≫ ν = 𝟙 _ := by
    apply (adj.homEquiv A _).injective
    rw [Adjunction.homEquiv_unit, Adjunction.homEquiv_unit]
    change adj.unit.app A ≫ (SheafOfModules.RingedTensor.restriction φ).map (μ ≫ ν) = _
    rw [Functor.map_comp, ← Category.assoc, scalarRingMap_unit]
    apply SheafOfModules.hom_ext
    apply PresheafOfModules.hom_ext
    intro X
    apply ModuleCat.hom_ext
    apply LinearMap.ext
    intro a
    change R.obj.obj X at a
    change ν.val.app X ((SheafOfModules.LocalizationCech.unitMap φ).val.app X a) =
      (adj.unit.app A).val.app X a
    calc
      _ = ν.val.app X (φ.hom.app X a) :=
        congrArg (fun b : B.obj.obj X ↦ ν.val.app X b)
          ((SheafOfModules.LocalizationCech.unitMap_existsUnique φ).choose_spec.1 X a)
      _ = (φ.hom.app X a) • (ν.val.app X (1 : B.obj.obj X)) := by
        simpa only [smul_eq_mul, mul_one] using
          (ν.val.app X).hom.map_smul (φ.hom.app X a) (1 : B.obj.obj X)
      _ = _ := by
        rw [scalarRingInverse_apply]
        have h := (adj.unit.app A).val.app X |>.hom.map_smul a (1 : R.obj.obj X)
        change (adj.unit.app A).val.app X (a * (1 : R.obj.obj X)) =
          (φ.hom.app X a) •
            (show ((SheafOfModules.RingedTensor.tensorFunctor φ).obj A).val.obj X from
              (adj.unit.app A).val.app X (1 : R.obj.obj X)) at h
        rw [mul_one] at h
        exact h.symm
  exact ⟨⟨ν, hμν, hνμ⟩⟩

private theorem extendedIdealMap_inclusion (I : RingedSiteIdeal R) (φ : R ⟶ B) :
    (SheafOfModules.RingedTensor.tensorFunctor φ).map I.inclusion ≫ scalarRingMap φ =
      extendedIdealMap I φ ≫ (I.extension φ).inclusion := by
  let adj := SheafOfModules.RingedTensor.tensorAdjunction φ
  apply (adj.homEquiv _ _).injective
  rw [Adjunction.homEquiv_naturality_left, Adjunction.homEquiv_naturality_right]
  change I.inclusion ≫ adj.homEquiv _ _ ((adj.homEquiv _ _).symm
      (SheafOfModules.LocalizationCech.unitMap φ)) =
    adj.homEquiv _ _ ((adj.homEquiv _ _).symm (idealCoefficientMap I φ)) ≫ _
  rw [Equiv.apply_symm_apply, Equiv.apply_symm_apply]
  exact idealCoefficientMap_inclusion I φ

/-- The scalar-extension unit is invertible on the quotient by an ideal subsheaf when the
coefficient morphism induces an isomorphism modulo that ideal.
Source: Stacks Project, Modules on Sites, Tags 03D7 and 03CY; Algebraization, Tag 099I.
(auxiliary; not a blueprint node).

Proof: sheafify the sectionwise quotient presheaves. The local kernel and lifting criteria
make their canonical comparison locally bijective, hence an isomorphism. Those sheaves are
the categorical cokernels of the ideal inclusions. Scalar extension preserves cokernels and
carries the rank-one ring module isomorphically to the target ring module. Its map from the
source ideal onto the extended ideal is epic: locally every extended-ideal section is a
finite linear combination of images of ideal sections, each of which lifts through the unit.
These presentations identify scalar extension of the source cokernel with the target
cokernel, and the adjunction unit becomes exactly the quotient comparison.
-/
theorem scalarExtension_unit_cokernel_isIso (I : RingedSiteIdeal R) (φ : R ⟶ B)
    (hquot : I.IsQuotientIso φ) :
    IsIso ((SheafOfModules.RingedTensor.tensorAdjunction φ).unit.app
      (cokernel I.inclusion)) := by
  let F := SheafOfModules.RingedTensor.tensorFunctor φ
  let G := SheafOfModules.RingedTensor.restriction φ
  let adj := SheafOfModules.RingedTensor.tensorAdjunction φ
  have : F.Additive := adj.left_adjoint_additive
  have : PreservesColimits F := adj.leftAdjoint_preservesColimits
  let μ := scalarRingMap φ
  have : IsIso μ := scalarRingMap_isIso φ
  let p := extendedIdealMap I φ
  have : Epi p := extendedIdealMap_epi I φ
  let a := I.inclusion
  let b := (I.extension φ).inclusion
  have hsquare : F.map a ≫ μ = p ≫ b := extendedIdealMap_inclusion I φ
  have hz : F.map a ≫ (μ ≫ cokernel.π b) = 0 := by
    rw [← Category.assoc, hsquare, Category.assoc, cokernel.condition, comp_zero]
  let d := CokernelCofork.ofπ (μ ≫ cokernel.π b) hz
  have hd : IsColimit d := by
    let h := isCokernelEpiComp (cokernelIsCokernel b) p hsquare
    exact IsCokernel.ofIso (F.map a ≫ μ) h d (Iso.refl _) (asIso μ).symm (Iso.refl _)
      (by simp) (by simp [d])
  let c := (CokernelCofork.ofπ (cokernel.π a) (cokernel.condition a)).map F
  let hc := CokernelCofork.mapIsColimit _ (cokernelIsCokernel a) F
  let e : F.obj (cokernel a) ≅ cokernel b :=
    hc.coconePointUniqueUpToIso hd
  have he : F.map (cokernel.π a) ≫ e.hom = μ ≫ cokernel.π b :=
    hc.comp_coconePointUniqueUpToIso_hom hd WalkingParallelPair.one
  have hn : adj.unit.app (cokernel a) ≫ G.map e.hom = cokernelCoefficientMap I φ := by
    apply (cancel_epi (cokernel.π a)).mp
    have ht := adj.unit.naturality (cokernel.π a)
    change cokernel.π a ≫ adj.unit.app (cokernel a) =
      adj.unit.app _ ≫ G.map (F.map (cokernel.π a)) at ht
    rw [← Category.assoc, ht, Category.assoc, ← G.map_comp, he,
      G.map_comp, ← Category.assoc, scalarRingMap_unit]
    exact (cokernel.π_desc _ _ _).symm
  have := cokernelCoefficientMap_isIso I φ hquot
  have : IsIso (adj.unit.app (cokernel a) ≫ G.map e.hom) := by rw [hn]; infer_instance
  exact IsIso.of_isIso_comp_right _ (G.map e.hom)

end CategoryTheory.RingedSiteIdeal
