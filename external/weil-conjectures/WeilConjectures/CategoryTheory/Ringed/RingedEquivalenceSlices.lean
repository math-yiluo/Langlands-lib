/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module
public import WeilConjectures.CategoryTheory.Ringed.RingedPresentationData
import Mathlib.CategoryTheory.Sites.CartesianMonoidal
import Mathlib.CategoryTheory.Comma.Over.Pullback
import Mathlib.CategoryTheory.Limits.Types.Pullbacks
import WeilConjectures.CategoryTheory.GeometricModuleConstruction
import Mathlib.Algebra.Category.Ring.Limits
import WeilConjectures.CategoryTheory.RingedSiteModules
import Mathlib.Algebra.Category.ModuleCat.Sheaf.Abelian
import WeilConjectures.CategoryTheory.RingedToposRingData
import WeilConjectures.CategoryTheory.Ringed.RingedToposMorphismSupplement
import WeilConjectures.CategoryTheory.AdjunctionRingOperations
import Mathlib.CategoryTheory.Monoidal.Cartesian.Basic
import Mathlib.CategoryTheory.Adjunction.Basic
import Mathlib.CategoryTheory.Sites.Equivalence
import Mathlib.CategoryTheory.Monoidal.CommGrp_
import WeilConjectures.Mathlib.CategoryTheory.Monoidal.Mod

/-! # Auxiliary ringed presentation comparisons -/

-- After pruning, this module only keeps private declarations.
set_option linter.privateModule false


@[expose] public noncomputable section

set_option autoImplicit false
universe u
open CategoryTheory CategoryTheory.Limits Opposite CategoryTheory.MonoidalCategory
namespace CategoryTheory
-- Cache the sheaf limit instances used repeatedly by the slice comparisons.
private instance (priority := 2000) sheafPullback
    {C : Type u} [SmallCategory C] {J : GrothendieckTopology C}
    {X Y Z : Sheaf J (Type u)} (f : X ⟶ Z) (g : Y ⟶ Z) :
    HasPullback f g := inferInstance

-- Products over a sheaf, and their images under the supplied fibre equivalences.
private def productOver {E : Type*} [Category E] [CartesianMonoidalCategory E]
    (A : E) : E ⥤ Over A where
  obj X := Over.mk (CartesianMonoidalCategory.fst A X)
  map f := Over.homMk (𝟙 A ⊗ₘ f) (by simp)
  map_id X := by apply Over.OverMorphism.ext; simp
  map_comp f g := by
    apply Over.OverMorphism.ext
    simp

private def productFibreIso {C : Type u} [SmallCategory C] {J : GrothendieckTopology C}
    {R : Sheaf J RingCat.{u}} (A : Sheaf J (Type u))
    (s : RingedSheafSliceAdjunctionData R A) :
    productOver A ⋙ s.fibreEquivalence.inverse ≅ elementSheafPullback A := by
  apply Functor.fullyFaithfulCancelRight (sheafToPresheaf (elementTopology A) (Type u))
  refine Functor.isoWhiskerLeft (productOver A) s.fibre_iso ≪≫ ?_
  refine NatIso.ofComponents (fun X ↦ NatIso.ofComponents (fun U ↦ ?_) ?_) ?_
  · exact Equiv.toIso
      { toFun := fun x ↦ x.val.2
        invFun := fun x ↦ ⟨(U.unop.unop.2, x), rfl⟩
        left_inv := fun x ↦ Subtype.ext (Prod.ext x.property.symm rfl)
        right_inv := fun x ↦ rfl }
  · intro U V f
    ext x
    rfl
  · intro X Y f
    ext U x
    rfl
private def productPostIso {E E' : Type*} [Category E] [Category E']
    [CartesianMonoidalCategory E] [CartesianMonoidalCategory E']
    (F : E ⥤ E') [PreservesFiniteLimits F] (A : E) :
    productOver A ⋙ Over.post F ≅ F ⋙ productOver (F.obj A) := by
  refine NatIso.ofComponents (fun X ↦ Over.isoMk
    (CartesianMonoidalCategory.prodComparisonIso F A X) ?_) ?_
  · exact CartesianMonoidalCategory.prodComparison_fst F A X
  · intro X Y f
    apply Over.OverMorphism.ext
    change F.map (𝟙 A ⊗ₘ f) ≫
      (CartesianMonoidalCategory.prodComparisonIso F A Y).hom =
      (CartesianMonoidalCategory.prodComparisonIso F A X).hom ≫ (𝟙 (F.obj A) ⊗ₘ F.map f)
    simpa only [Functor.map_id, CartesianMonoidalCategory.prodComparisonIso_hom] using
      CartesianMonoidalCategory.prodComparison_natural F (𝟙 A) f
private def sliceEquivalence {C D : Type u} [SmallCategory C] [SmallCategory D]
    {J : GrothendieckTopology C} {K : GrothendieckTopology D}
    {R : Sheaf J RingCat.{u}} {S : Sheaf K RingCat.{u}}
    (F : Sheaf K (Type u) ⥤ Sheaf J (Type u)) [F.IsEquivalence]
    (A : Sheaf K (Type u)) (s : RingedSheafSliceAdjunctionData S A)
    (t : RingedSheafSliceAdjunctionData R (F.obj A)) :
    Sheaf (elementTopology A) (Type u) ≌ Sheaf (elementTopology (F.obj A)) (Type u) :=
  s.fibreEquivalence.trans ((Over.post F).asEquivalence.trans t.fibreEquivalence.symm)

private def sliceComparison {C D : Type u} [SmallCategory C] [SmallCategory D]
    {J : GrothendieckTopology C} {K : GrothendieckTopology D}
    {R : Sheaf J RingCat.{u}} {S : Sheaf K RingCat.{u}}
    (F : Sheaf K (Type u) ⥤ Sheaf J (Type u)) [F.IsEquivalence]
    (A : Sheaf K (Type u)) (s : RingedSheafSliceAdjunctionData S A)
    (t : RingedSheafSliceAdjunctionData R (F.obj A)) :
    F ⋙ elementSheafPullback (F.obj A) ≅
      elementSheafPullback A ⋙ (sliceEquivalence F A s t).functor := by
  let p := productFibreIso A s
  let q := productFibreIso (F.obj A) t
  let h : F ⋙ elementSheafPullback (F.obj A) ≅
      (productOver A ⋙ Over.post F) ⋙ t.fibreEquivalence.inverse :=
    Functor.isoWhiskerLeft F q.symm ≪≫
      (Functor.associator _ _ _).symm ≪≫
      Functor.isoWhiskerRight (productPostIso F A).symm t.fibreEquivalence.inverse
  let r : productOver A ≅ elementSheafPullback A ⋙ s.fibreEquivalence.functor :=
    (Functor.rightUnitor _).symm ≪≫
      Functor.isoWhiskerLeft _ s.fibreEquivalence.counitIso.symm ≪≫
      (Functor.associator _ _ _).symm ≪≫
      Functor.isoWhiskerRight p s.fibreEquivalence.functor
  exact h ≪≫ Functor.isoWhiskerRight
    (Functor.isoWhiskerRight r (Over.post F)) t.fibreEquivalence.inverse
private theorem binary_conjugate
    {E E' : Type*} [Category E] [Category E'] [CartesianMonoidalCategory E']
    {F G : E ⥤ E'} (α : F ≅ G)
    {X₁ X₂ X₃ X₁₂ : E} (p₁ : X₁₂ ⟶ X₁) (p₂ : X₁₂ ⟶ X₂)
    (a : X₁₂ ⟶ X₃) {Y₁ Y₂ Y₃ : E'}
    (r₁ : F.obj X₁ ⟶ Y₁) (r₂ : F.obj X₂ ⟶ Y₂) (r₃ : F.obj X₃ ⟶ Y₃)
    (b : Y₁ ⊗ Y₂ ⟶ Y₃)
    (h : F.map a ≫ r₃ = CartesianMonoidalCategory.lift
      (F.map p₁ ≫ r₁) (F.map p₂ ≫ r₂) ≫ b) :
    G.map a ≫ α.inv.app X₃ ≫ r₃ = CartesianMonoidalCategory.lift
      (G.map p₁ ≫ α.inv.app X₁ ≫ r₁)
      (G.map p₂ ≫ α.inv.app X₂ ≫ r₂) ≫ b := by
  rw [α.inv.naturality_assoc, h, CartesianMonoidalCategory.comp_lift_assoc]
  rw [← α.inv.naturality_assoc, ← α.inv.naturality_assoc]

private abbrev ringSets {C : Type u} [SmallCategory C] {J : GrothendieckTopology C}
    (R : Sheaf J RingCat.{u}) := (sheafCompose J (forget RingCat)).obj R

private abbrev ringSections {C : Type u} [SmallCategory C]
    {J : GrothendieckTopology C} (R : Sheaf J RingCat.{u}) (U : Cᵒᵖ) :
    Ring ((ringSets R).obj.obj U) := inferInstanceAs (Ring (R.obj.obj U))
attribute [local instance] ringSections

private def ringBinary {C : Type u} [SmallCategory C] {J : GrothendieckTopology C}
    (R : Sheaf J RingCat.{u}) (op : ∀ U : Cᵒᵖ, R.obj.obj U → R.obj.obj U → R.obj.obj U)
    (hn : ∀ {U V : Cᵒᵖ} (f : U ⟶ V) x y,
      R.obj.map f (op U x y) = op V (R.obj.map f x) (R.obj.map f y)) :
    ringSets R ⊗ ringSets R ⟶ ringSets R :=
  ⟨{ app := fun U ↦ TypeCat.ofHom (fun x ↦ op U x.1 x.2)
     naturality := by intro U V f; ext x; exact (hn f x.1 x.2).symm }⟩

private def ringAdd {C : Type u} [SmallCategory C] {J : GrothendieckTopology C}
    (R : Sheaf J RingCat.{u}) : ringSets R ⊗ ringSets R ⟶ ringSets R :=
  ringBinary R (fun _ x y ↦ x + y) (fun f x y ↦ (R.obj.map f).hom.map_add x y)

private def ringMul {C : Type u} [SmallCategory C] {J : GrothendieckTopology C}
    (R : Sheaf J RingCat.{u}) : ringSets R ⊗ ringSets R ⟶ ringSets R :=
  ringBinary R (fun _ x y ↦ x * y) (fun f x y ↦ (R.obj.map f).hom.map_mul x y)

private theorem ringAdd_eq {C : Type u} [SmallCategory C] {J : GrothendieckTopology C}
    (R : Sheaf J RingCat.{u}) {T : Sheaf J (Type u)}
    (x y z : T ⟶ ringSets R) (h : ∀ U t,
      z.hom.app U t = @Add.add (R.obj.obj U) inferInstance (x.hom.app U t) (y.hom.app U t)) :
    z = CartesianMonoidalCategory.lift x y ≫ ringAdd R := by
  ext U t
  exact h U t

private theorem ringMul_eq {C : Type u} [SmallCategory C] {J : GrothendieckTopology C}
    (R : Sheaf J RingCat.{u}) {T : Sheaf J (Type u)}
    (x y z : T ⟶ ringSets R) (h : ∀ U t,
      z.hom.app U t = @Mul.mul (R.obj.obj U) inferInstance (x.hom.app U t) (y.hom.app U t)) :
    z = CartesianMonoidalCategory.lift x y ≫ ringMul R := by
  ext U t
  exact h U t
private def ringZero {C : Type u} [SmallCategory C] {J : GrothendieckTopology C}
    (R : Sheaf J RingCat.{u}) : 𝟙_ (Sheaf J (Type u)) ⟶ ringSets R :=
  RingedToposMorphism.RingData.zero _

private def ringOne {C : Type u} [SmallCategory C] {J : GrothendieckTopology C}
    (R : Sheaf J RingCat.{u}) : 𝟙_ (Sheaf J (Type u)) ⟶ ringSets R :=
  RingedToposMorphism.RingData.one _

private theorem ringData_add {C D : Type u} [SmallCategory C] [SmallCategory D]
    {J : GrothendieckTopology C} {K : GrothendieckTopology D}
    {R : Sheaf J RingCat.{u}} {S : Sheaf K RingCat.{u}}
    (e : RingedToposMorphism.RingData R S) :
    e.inverse.map (ringAdd S) ≫ e.ringMap = CartesianMonoidalCategory.lift
      (e.inverse.map (CartesianMonoidalCategory.fst _ _) ≫ e.ringMap)
      (e.inverse.map (CartesianMonoidalCategory.snd _ _) ≫ e.ringMap) ≫ ringAdd R := by
  ext U t
  exact e.ring_add _ _ _ _ (fun _ _ ↦ rfl) U t

private theorem ringData_mul {C D : Type u} [SmallCategory C] [SmallCategory D]
    {J : GrothendieckTopology C} {K : GrothendieckTopology D}
    {R : Sheaf J RingCat.{u}} {S : Sheaf K RingCat.{u}}
    (e : RingedToposMorphism.RingData R S) :
    e.inverse.map (ringMul S) ≫ e.ringMap = CartesianMonoidalCategory.lift
      (e.inverse.map (CartesianMonoidalCategory.fst _ _) ≫ e.ringMap)
      (e.inverse.map (CartesianMonoidalCategory.snd _ _) ≫ e.ringMap) ≫ ringMul R := by
  ext U t
  exact e.ring_mul _ _ _ _ (fun _ _ ↦ rfl) U t

-- Transport the ring operations through the product/fibre comparison.
private abbrev restrictSets {C C' : Type u} [SmallCategory C] [SmallCategory C']
    {J : GrothendieckTopology C} {J' : GrothendieckTopology C'}
    (F : C' ⥤ C) [Functor.IsContinuous F J' J] :=
  F.sheafPushforwardContinuous (Type u) J' J

-- Fibrewise pullbacks give the further-restriction comparison.
private def pullbackSections {C : Type u} [SmallCategory C]
    {J : GrothendieckTopology C} {X Y Z : Sheaf J (Type u)}
    (f : X ⟶ Z) (g : Y ⟶ Z) (U : Cᵒᵖ) :
    (pullback f g).obj.obj U ≃
      {p : X.obj.obj U × Y.obj.obj U // f.hom.app U p.1 = g.hom.app U p.2} :=
  PullbackCone.IsLimit.equivPullbackObj
    (isLimitPullbackConeMapOfIsLimit
      (sheafToPresheaf J (Type u) ⋙ (evaluation Cᵒᵖ (Type u)).obj U)
      (pullback.condition (f := f) (g := g)) (pullbackIsPullback f g))

private theorem pullbackSections_fst {C : Type u} [SmallCategory C]
    {J : GrothendieckTopology C} {X Y Z : Sheaf J (Type u)}
    (f : X ⟶ Z) (g : Y ⟶ Z) (U : Cᵒᵖ) (x : (pullback f g).obj.obj U) :
    (pullbackSections f g U x).val.1 = (pullback.fst f g).hom.app U x :=
  PullbackCone.IsLimit.equivPullbackObj_apply_fst _ _

private theorem pullbackSections_snd {C : Type u} [SmallCategory C]
    {J : GrothendieckTopology C} {X Y Z : Sheaf J (Type u)}
    (f : X ⟶ Z) (g : Y ⟶ Z) (U : Cᵒᵖ) (x : (pullback f g).obj.obj U) :
    (pullbackSections f g U x).val.2 = (pullback.snd f g).hom.app U x :=
  PullbackCone.IsLimit.equivPullbackObj_apply_snd _ _

private theorem pullbackSection_ext {C : Type u} [SmallCategory C]
    {J : GrothendieckTopology C} {X Y Z : Sheaf J (Type u)}
    (f : X ⟶ Z) (g : Y ⟶ Z) (U : Cᵒᵖ) {x y : (pullback f g).obj.obj U}
    (hf : (pullback.fst f g).hom.app U x = (pullback.fst f g).hom.app U y)
    (hg : (pullback.snd f g).hom.app U x = (pullback.snd f g).hom.app U y) : x = y := by
  apply (pullbackSections f g U).injective
  apply Subtype.ext
  exact Prod.ext ((pullbackSections_fst f g U x).trans
    (hf.trans (pullbackSections_fst f g U y).symm))
    ((pullbackSections_snd f g U x).trans (hg.trans (pullbackSections_snd f g U y).symm))

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true

-- Compatibility of the product comparisons with further restriction.
attribute [irreducible] sliceComparison


-- Recover module inverse images from their specified adjunctions and linearity.
private abbrev moduleSet {C : Type u} [SmallCategory C] {J : GrothendieckTopology C}
    (R : Sheaf J RingCat.{u}) :=
  SheafOfModules.toSheaf.{u} R ⋙ sheafCompose J (forget AddCommGrpCat.{u})

private def moduleAdd {C : Type u} [SmallCategory C] {J : GrothendieckTopology C}
    {R : Sheaf J RingCat.{u}} (M : ringedSiteModules.{u} R) :
    (moduleSet R).obj M ⊗ (moduleSet R).obj M ⟶ (moduleSet R).obj M :=
  ⟨{ app := fun U ↦ TypeCat.ofHom (fun x ↦ @Add.add (M.val.obj U) inferInstance x.1 x.2)
     naturality := by intro U V f; ext x; exact (M.val.map f).hom.map_add _ _ |>.symm }⟩

private def moduleSMul {C : Type u} [SmallCategory C] {J : GrothendieckTopology C}
    {R : Sheaf J RingCat.{u}} (M : ringedSiteModules.{u} R) :
    ringSets R ⊗ (moduleSet R).obj M ⟶ (moduleSet R).obj M :=
  ⟨{ app := fun U ↦ TypeCat.ofHom (fun x ↦
         @SMul.smul (R.obj.obj U) (M.val.obj U) inferInstance x.1 x.2)
     naturality := by intro U V f; ext x; exact (M.val.map_smul f _ _).symm }⟩

private def inverseModulesIso {C D : Type u} [SmallCategory C] [SmallCategory D]
    {J : GrothendieckTopology C} {K : GrothendieckTopology D}
    {R : Sheaf J RingCat.{u}} {S : Sheaf K RingCat.{u}}
    (e : RingedToposMorphism R S) [e.inverse.IsEquivalence]
    (W : ringedSiteModules.{u} S ≌ ringedSiteModules.{u} R)
    (p : W.inverse ≅ e.modules) :
    moduleSet S ⋙ e.inverse ≅ W.functor ⋙ moduleSet R := by
  let a : W.functor ⊣ e.modules := W.toAdjunction.ofNatIsoRight p
  let v : moduleSet S ≅ W.functor ⋙ (moduleSet R ⋙ e.direct) :=
    Functor.isoWhiskerRight (asIso a.unit) (moduleSet S) ≪≫
      Functor.associator _ _ _ ≪≫ Functor.isoWhiskerLeft W.functor e.underlying
  exact Functor.isoWhiskerRight v e.inverse ≪≫
    Functor.associator _ _ _ ≪≫
    Functor.isoWhiskerLeft W.functor (Functor.associator _ _ _) ≪≫
    Functor.isoWhiskerLeft (W.functor ⋙ moduleSet R) (asIso e.adj.counit) ≪≫
    Functor.rightUnitor _

attribute [irreducible] inverseModulesIso

private theorem inverseModulesIso_formula
    {C D : Type u} [SmallCategory C] [SmallCategory D]
    {J : GrothendieckTopology C} {K : GrothendieckTopology D}
    {R : Sheaf J RingCat.{u}} {S : Sheaf K RingCat.{u}}
    (e : RingedToposMorphism R S) [e.inverse.IsEquivalence]
    (W : ringedSiteModules.{u} S ≌ ringedSiteModules.{u} R)
    (p : W.inverse ≅ e.modules) (M : ringedSiteModules.{u} S)
    {T : Sheaf K (Type u)} (x : T ⟶ (moduleSet S).obj M) :
    e.inverse.map x ≫ (inverseModulesIso e W p).hom.app M =
      (e.adj.homEquiv _ _).symm
        (x ≫ (moduleSet S).map ((W.toAdjunction.ofNatIsoRight p).unit.app M) ≫
          e.underlying.hom.app (W.functor.obj M)) := by
  simp only [Adjunction.homEquiv_symm_apply, inverseModulesIso, Iso.trans_hom,
    Functor.isoWhiskerRight_hom, Functor.isoWhiskerLeft_hom,
    Functor.whiskerRight_app, Functor.whiskerLeft_app,
    NatTrans.comp_app, Functor.associator_hom_app, Functor.rightUnitor_hom_app,
    asIso_hom, Functor.map_comp, Functor.comp_obj, Functor.comp_map,
    Category.id_comp, Category.assoc]
  ext U t
  rfl

private theorem inverseModulesIso_linear
    {C D : Type u} [SmallCategory C] [SmallCategory D]
    {J : GrothendieckTopology C} {K : GrothendieckTopology D}
    {R : Sheaf J RingCat.{u}} {S : Sheaf K RingCat.{u}}
    (e : RingedToposMorphism R S) [e.inverse.IsEquivalence]
    (W : ringedSiteModules.{u} S ≌ ringedSiteModules.{u} R)
    (p : W.inverse ≅ e.modules) (M : ringedSiteModules.{u} S)
    (T : Sheaf K (Type u)) (a : T ⟶ ringSets S)
    (x y z : T ⟶ (moduleSet S).obj M)
    (hz : ∀ U t, z.hom.app U t =
      @Add.add (M.val.obj U) inferInstance
        (@SMul.smul (S.obj.obj U) (M.val.obj U) inferInstance
          (a.hom.app U t) (x.hom.app U t)) (y.hom.app U t)) :
    ∀ U t, (e.inverse.map z ≫ (inverseModulesIso e W p).hom.app M).hom.app U t =
      @Add.add ((W.functor.obj M).val.obj U) inferInstance
        (@SMul.smul (R.obj.obj U) ((W.functor.obj M).val.obj U) inferInstance
          ((e.inverse.map a ≫ e.ringMap).hom.app U t)
          ((e.inverse.map x ≫ (inverseModulesIso e W p).hom.app M).hom.app U t))
        ((e.inverse.map y ≫ (inverseModulesIso e W p).hom.app M).hom.app U t) := by
  let f := (W.toAdjunction.ofNatIsoRight p).unit.app M
  intro U t
  rw [inverseModulesIso_formula, inverseModulesIso_formula, inverseModulesIso_formula]
  apply e.module_linear (W.functor.obj M) T a
    (x ≫ (moduleSet S).map f) (y ≫ (moduleSet S).map f)
    (z ≫ (moduleSet S).map f)
  intro V v
  change f.val.app V (z.hom.app V v) = _
  rw [hz]
  change f.val.app V ((_ : S.obj.obj V) • (_ : M.val.obj V) +
    (_ : M.val.obj V)) = _
  exact (f.val.app V).hom.map_add _ _ |>.trans
    (congrArg (fun z ↦ z + f.val.app V (y.hom.app V v))
      ((f.val.app V).hom.map_smul _ _))
private theorem inverseModulesIso_add
    {C D : Type u} [SmallCategory C] [SmallCategory D]
    {J : GrothendieckTopology C} {K : GrothendieckTopology D}
    {R : Sheaf J RingCat.{u}} {S : Sheaf K RingCat.{u}}
    (e : RingedToposMorphism R S) [e.inverse.IsEquivalence]
    (W : ringedSiteModules.{u} S ≌ ringedSiteModules.{u} R)
    (p : W.inverse ≅ e.modules) (M : ringedSiteModules.{u} S) :
    e.inverse.map (moduleAdd M) ≫ (inverseModulesIso e W p).hom.app M =
      CartesianMonoidalCategory.lift
        (e.inverse.map (CartesianMonoidalCategory.fst _ _) ≫
          (inverseModulesIso e W p).hom.app M)
        (e.inverse.map (CartesianMonoidalCategory.snd _ _) ≫
          (inverseModulesIso e W p).hom.app M) ≫ moduleAdd (W.functor.obj M) := by
  ext U t
  have h := inverseModulesIso_linear e W p M _
    (RingedToposMorphism.RingData.one _)
    (CartesianMonoidalCategory.fst _ _) (CartesianMonoidalCategory.snd _ _)
    (moduleAdd M) (fun V x ↦ by
      change @Add.add (M.val.obj V) inferInstance x.1 x.2 =
        @Add.add (M.val.obj V) inferInstance
          (@SMul.smul (S.obj.obj V) (M.val.obj V) inferInstance 1 x.1) x.2
      exact congrArg (fun z : M.val.obj V ↦ z + (show M.val.obj V from x.2))
        (@one_smul (S.obj.obj V) (M.val.obj V) _ _ x.1).symm) U t
  rw [e.ring_one _ _ (fun _ _ ↦ rfl)] at h
  change _ = (1 : R.obj.obj U) • (_ : (W.functor.obj M).val.obj U) +
    (_ : (W.functor.obj M).val.obj U) at h
  rw [one_smul] at h
  exact h

private def moduleZero {C : Type u} [SmallCategory C] {J : GrothendieckTopology C}
    {R : Sheaf J RingCat.{u}} (M : ringedSiteModules.{u} R) (T : Sheaf J (Type u)) :
    T ⟶ (moduleSet R).obj M :=
  ⟨{ app := fun U ↦ TypeCat.ofHom (fun _ ↦ (0 : M.val.obj U))
     naturality := by intro U V f; ext x; exact (map_zero (M.val.map f).hom).symm }⟩

private theorem inverseModulesIso_smul
    {C D : Type u} [SmallCategory C] [SmallCategory D]
    {J : GrothendieckTopology C} {K : GrothendieckTopology D}
    {R : Sheaf J RingCat.{u}} {S : Sheaf K RingCat.{u}}
    (e : RingedToposMorphism R S) [e.inverse.IsEquivalence]
    (W : ringedSiteModules.{u} S ≌ ringedSiteModules.{u} R)
    (p : W.inverse ≅ e.modules) (M : ringedSiteModules.{u} S) :
    e.inverse.map (moduleSMul M) ≫ (inverseModulesIso e W p).hom.app M =
      CartesianMonoidalCategory.lift
        (e.inverse.map (CartesianMonoidalCategory.fst _ _) ≫ e.ringMap)
        (e.inverse.map (CartesianMonoidalCategory.snd _ _) ≫
          (inverseModulesIso e W p).hom.app M) ≫ moduleSMul (W.functor.obj M) := by
  have hz (T : Sheaf K (Type u)) (U : Cᵒᵖ) (t : (e.inverse.obj T).obj.obj U) :
      (e.inverse.map (moduleZero M T) ≫ (inverseModulesIso e W p).hom.app M).hom.app U t =
        (0 : (W.functor.obj M).val.obj U) := by
    have h := inverseModulesIso_linear e W p M T
      (RingedToposMorphism.RingData.one T) (moduleZero M T)
      (moduleZero M T) (moduleZero M T) (fun V x ↦ by
        change (0 : M.val.obj V) = (1 : S.obj.obj V) • (0 : M.val.obj V) + 0
        simp) U t
    rw [e.ring_one _ _ (fun _ _ ↦ rfl)] at h
    change _ = (1 : R.obj.obj U) • (_ : (W.functor.obj M).val.obj U) +
      (_ : (W.functor.obj M).val.obj U) at h
    rw [one_smul] at h
    have hh : (show (W.functor.obj M).val.obj U from
        (e.inverse.map (moduleZero M T) ≫
          (inverseModulesIso e W p).hom.app M).hom.app U t) =
        (show (W.functor.obj M).val.obj U from
        (e.inverse.map (moduleZero M T) ≫
          (inverseModulesIso e W p).hom.app M).hom.app U t) +
        (show (W.functor.obj M).val.obj U from
        (e.inverse.map (moduleZero M T) ≫
          (inverseModulesIso e W p).hom.app M).hom.app U t) := h
    exact @add_eq_left ((W.functor.obj M).val.obj U) _ _ _ _ |>.mp hh.symm
  ext U t
  have h := inverseModulesIso_linear e W p M _
    (CartesianMonoidalCategory.fst _ _) (CartesianMonoidalCategory.snd _ _)
    (moduleZero M _) (moduleSMul M) (fun V x ↦ by
      exact (@add_zero (M.val.obj V) _
        (@SMul.smul (S.obj.obj V) (M.val.obj V) inferInstance x.1 x.2)).symm) U t
  rw [hz] at h
  change _ = (_ : R.obj.obj U) • (_ : (W.functor.obj M).val.obj U) +
    (0 : (W.functor.obj M).val.obj U) at h
  rw [add_zero] at h
  exact h

private theorem compare_binary
    {E E' : Type*} [Category E] [Category E']
    [CartesianMonoidalCategory E] [CartesianMonoidalCategory E']
    (F G : E ⥤ E') [PreservesFiniteLimits F] (q : F ≅ G)
    {X₁ X₂ X₃ : E} {Y₁ Y₂ Y₃ Z₁ Z₂ Z₃ : E'}
    (d₁ : F.obj X₁ ≅ Y₁) (d₂ : F.obj X₂ ≅ Y₂) (d₃ : F.obj X₃ ≅ Y₃)
    (t₁ : G.obj X₁ ≅ Z₁) (t₂ : G.obj X₂ ≅ Z₂) (t₃ : G.obj X₃ ≅ Z₃)
    (a : X₁ ⊗ X₂ ⟶ X₃) (b : Y₁ ⊗ Y₂ ⟶ Y₃) (c : Z₁ ⊗ Z₂ ⟶ Z₃)
    (hd : F.map a ≫ d₃.hom = CartesianMonoidalCategory.lift
      (F.map (CartesianMonoidalCategory.fst _ _) ≫ d₁.hom)
      (F.map (CartesianMonoidalCategory.snd _ _) ≫ d₂.hom) ≫ b)
    (ht : G.map a ≫ t₃.hom = CartesianMonoidalCategory.lift
      (G.map (CartesianMonoidalCategory.fst _ _) ≫ t₁.hom)
      (G.map (CartesianMonoidalCategory.snd _ _) ≫ t₂.hom) ≫ c) :
    b ≫ (d₃.symm ≪≫ q.app X₃ ≪≫ t₃).hom =
      ((d₁.symm ≪≫ q.app X₁ ≪≫ t₁).hom ⊗ₘ
        (d₂.symm ≪≫ q.app X₂ ≪≫ t₂).hom) ≫ c := by
  let P := CartesianMonoidalCategory.prodComparisonIso F X₁ X₂ ≪≫ (d₁ ⊗ᵢ d₂)
  apply (cancel_epi P.hom).mp
  have hP : P.hom = CartesianMonoidalCategory.lift
      (F.map (CartesianMonoidalCategory.fst _ _) ≫ d₁.hom)
      (F.map (CartesianMonoidalCategory.snd _ _) ≫ d₂.hom) := by
    simp only [P, Iso.trans_hom, tensorIso_hom,
      CartesianMonoidalCategory.prodComparisonIso_hom,
      CartesianMonoidalCategory.prodComparison, CartesianMonoidalCategory.lift_map]
  simp only [Iso.trans_hom, Iso.symm_hom, Iso.app_hom]
  rw [← Category.assoc, hP, ← hd]
  simp only [Category.assoc, Iso.hom_inv_id_assoc]
  rw [q.hom.naturality_assoc, ht, CartesianMonoidalCategory.comp_lift_assoc]
  simp only [← q.hom.naturality_assoc]
  rw [CartesianMonoidalCategory.lift_map_assoc]
  simp only [Category.assoc, Iso.hom_inv_id_assoc]

private def liftModuleMap {C : Type u} [SmallCategory C] {J : GrothendieckTopology C}
    {R : Sheaf J RingCat.{u}} {M N : ringedSiteModules.{u} R}
    (f : (moduleSet R).obj M ⟶ (moduleSet R).obj N)
    (ha : ∀ U (x y : M.val.obj U), f.hom.app U (x + y) =
      @Add.add (N.val.obj U) inferInstance (f.hom.app U x) (f.hom.app U y))
    (hs : ∀ U (r : R.obj.obj U) (x : M.val.obj U), f.hom.app U (r • x) =
      @SMul.smul (R.obj.obj U) (N.val.obj U) inferInstance r (f.hom.app U x)) : M ⟶ N where
  val :=
    { app U := ModuleCat.ofHom
        { toFun := f.hom.app U
          map_add' := ha U
          map_smul' := hs U }
      naturality := by
        intro U V g
        ext x
        exact congrArg (fun h ↦ h x) (f.hom.naturality g) }

private def liftModuleIso {C : Type u} [SmallCategory C] {J : GrothendieckTopology C}
    {R : Sheaf J RingCat.{u}} {M N : ringedSiteModules.{u} R}
    (f : (moduleSet R).obj M ≅ (moduleSet R).obj N)
    (ha : ∀ U (x y : M.val.obj U), f.hom.hom.app U (x + y) =
      @Add.add (N.val.obj U) inferInstance (f.hom.hom.app U x) (f.hom.hom.app U y))
    (hs : ∀ U (r : R.obj.obj U) (x : M.val.obj U), f.hom.hom.app U (r • x) =
      @SMul.smul (R.obj.obj U) (N.val.obj U) inferInstance r (f.hom.hom.app U x)) : M ≅ N := by
  let e (U : Cᵒᵖ) : M.val.obj U ≃ N.val.obj U :=
    ((sheafToPresheaf J (Type u)).mapIso f).app U |>.toEquiv
  have ei (U : Cᵒᵖ) (x : M.val.obj U) : e U x = f.hom.hom.app U x := rfl
  have he (U : Cᵒᵖ) (x : N.val.obj U) : (e U).symm x = f.inv.hom.app U x := rfl
  refine
    { hom := liftModuleMap f.hom ha hs
      inv := liftModuleMap f.inv ?_ ?_
      hom_inv_id := by ext U x; exact (e U).symm_apply_apply x
      inv_hom_id := by ext U x; exact (e U).apply_symm_apply x }
  · intro U x y
    apply (e U).injective
    change e U ((e U).symm (x + y)) =
      e U ((e U).symm x + (e U).symm y)
    rw [(e U).apply_symm_apply, ei, ha]
    change x + y = e U ((e U).symm x) + e U ((e U).symm y)
    rw [(e U).apply_symm_apply, (e U).apply_symm_apply]
  · intro U r x
    apply (e U).injective
    change e U ((e U).symm (r • x)) = e U (r • (e U).symm x)
    rw [(e U).apply_symm_apply, ei, hs]
    exact congrArg (fun y ↦ r • y) ((e U).apply_symm_apply x).symm

private abbrev restrictRing {C C' : Type u} [SmallCategory C] [SmallCategory C']
    {J : GrothendieckTopology C} {J' : GrothendieckTopology C'}
    (F : C' ⥤ C) [Functor.IsContinuous F J' J] (R : Sheaf J RingCat.{u}) :=
  (F.sheafPushforwardContinuous RingCat.{u} J' J).obj R

-- Use precomposition internally; compare explicitly with scalar restriction by identity.
private def restrictModules {C C' : Type u} [SmallCategory C] [SmallCategory C']
    {J : GrothendieckTopology C} {J' : GrothendieckTopology C'}
    (F : C' ⥤ C) [Functor.IsContinuous F J' J] (R : Sheaf J RingCat.{u}) :
    ringedSiteModules.{u} R ⥤ ringedSiteModules.{u} (restrictRing (J' := J') F R) where
  obj M :=
    { val := (PresheafOfModules.pushforward₀ F R.obj).obj M.val
      isSheaf := ((F.sheafPushforwardContinuous _ J' J).obj ⟨_, M.isSheaf⟩).property }
  map f := ⟨(PresheafOfModules.pushforward₀ F R.obj).map f.val⟩

private theorem restrict_lift
    {C C' : Type u} [SmallCategory C] [SmallCategory C']
    {J : GrothendieckTopology C} {J' : GrothendieckTopology C'}
    (F : C' ⥤ C) [Functor.IsContinuous F J' J]
    {X Y Z : Sheaf J (Type u)} (f : X ⟶ Y) (g : X ⟶ Z) :
    (restrictSets (J' := J') F).map (CartesianMonoidalCategory.lift f g) =
      CartesianMonoidalCategory.lift ((restrictSets (J' := J') F).map f)
        ((restrictSets (J' := J') F).map g) := by
  ext U x
  rfl

private def restrictUnderlying
    {C C' : Type u} [SmallCategory C] [SmallCategory C']
    {J : GrothendieckTopology C} {J' : GrothendieckTopology C'}
    (F : C' ⥤ C) [Functor.IsContinuous F J' J] (R : Sheaf J RingCat.{u}) :
    restrictModules (J' := J') F R ⋙ moduleSet (restrictRing F R) ≅
      moduleSet R ⋙ restrictSets (J' := J') F := by
  refine NatIso.ofComponents (fun M ↦ ?_) ?_
  · exact Iso.refl _
  · intro M N f
    ext U x
    rfl
private def moduleSquareSets
    {C D C' D' : Type u}
    [SmallCategory C] [SmallCategory D] [SmallCategory C'] [SmallCategory D']
    {J : GrothendieckTopology C} {K : GrothendieckTopology D}
    {J' : GrothendieckTopology C'} {K' : GrothendieckTopology D'}
    {R : Sheaf J RingCat.{u}} {S : Sheaf K RingCat.{u}}
    (F : C' ⥤ C) (G : D' ⥤ D)
    [Functor.IsContinuous F J' J] [Functor.IsContinuous G K' K]
    (e : RingedToposMorphism R S) [e.inverse.IsEquivalence]
    (e' : RingedToposMorphism (restrictRing F R) (restrictRing G S))
    [e'.inverse.IsEquivalence]
    (q : e.inverse ⋙ restrictSets (J' := J') F ≅ restrictSets (J' := K') G ⋙ e'.inverse)
    (W : ringedSiteModules.{u} S ≌ ringedSiteModules.{u} R) (p : W.inverse ≅ e.modules)
    (W' : ringedSiteModules.{u} (restrictRing G S) ≌
      ringedSiteModules.{u} (restrictRing (J' := J') F R)) (p' : W'.inverse ≅ e'.modules) :
    (W.functor ⋙ restrictModules (J' := J') F R) ⋙ moduleSet (restrictRing F R) ≅
      (restrictModules (J' := K') G S ⋙ W'.functor) ⋙ moduleSet (restrictRing F R) := by
  let d := Functor.isoWhiskerLeft W.functor (restrictUnderlying F R) ≪≫
    Functor.isoWhiskerRight (inverseModulesIso e W p).symm (restrictSets (J' := J') F)
  let a := Functor.isoWhiskerLeft (moduleSet S) q
  let t := Functor.isoWhiskerRight (restrictUnderlying G S).symm e'.inverse ≪≫
    Functor.isoWhiskerLeft (restrictModules (J' := K') G S) (inverseModulesIso e' W' p')
  exact d ≪≫ a ≪≫ t

private theorem moduleSquareSets_hom
    {C D C' D' : Type u}
    [SmallCategory C] [SmallCategory D] [SmallCategory C'] [SmallCategory D']
    {J : GrothendieckTopology C} {K : GrothendieckTopology D}
    {J' : GrothendieckTopology C'} {K' : GrothendieckTopology D'}
    {R : Sheaf J RingCat.{u}} {S : Sheaf K RingCat.{u}}
    (F : C' ⥤ C) (G : D' ⥤ D)
    [Functor.IsContinuous F J' J] [Functor.IsContinuous G K' K]
    (e : RingedToposMorphism R S) [e.inverse.IsEquivalence]
    (e' : RingedToposMorphism (restrictRing F R) (restrictRing G S))
    [e'.inverse.IsEquivalence]
    (q : e.inverse ⋙ restrictSets (J' := J') F ≅ restrictSets (J' := K') G ⋙ e'.inverse)
    (W : ringedSiteModules.{u} S ≌ ringedSiteModules.{u} R) (p : W.inverse ≅ e.modules)
    (W' : ringedSiteModules.{u} (restrictRing G S) ≌
      ringedSiteModules.{u} (restrictRing (J' := J') F R)) (p' : W'.inverse ≅ e'.modules)
    (M : ringedSiteModules.{u} S) :
    (moduleSquareSets F G e e' q W p W' p').hom.app M =
      (restrictSets (J' := J') F).map ((inverseModulesIso e W p).inv.app M) ≫
        q.hom.app ((moduleSet S).obj M) ≫
          (inverseModulesIso e' W' p').hom.app
            ((restrictModules (J' := K') G S).obj M) := by
  simp only [moduleSquareSets, Iso.trans_hom, Iso.symm_hom,
    Functor.isoWhiskerLeft_hom, Functor.isoWhiskerRight_hom,
    Functor.whiskerLeft_app, Functor.whiskerRight_app, NatTrans.comp_app,
    restrictUnderlying, NatIso.ofComponents_hom_app, NatIso.ofComponents_inv_app,
    Iso.refl_hom, Iso.refl_inv, Category.assoc]
  dsimp only [Functor.comp_obj]
  erw [e'.inverse.map_id]
  simp only [Category.id_comp]

attribute [irreducible] moduleSquareSets

-- A compatible square of set inverse images lifts to a square of module inverse images.
private def moduleSquare
    {C D C' D' : Type u}
    [SmallCategory C] [SmallCategory D] [SmallCategory C'] [SmallCategory D']
    {J : GrothendieckTopology C} {K : GrothendieckTopology D}
    {J' : GrothendieckTopology C'} {K' : GrothendieckTopology D'}
    {R : Sheaf J RingCat.{u}} {S : Sheaf K RingCat.{u}}
    (F : C' ⥤ C) (G : D' ⥤ D)
    [Functor.IsContinuous F J' J] [Functor.IsContinuous G K' K]
    (e : RingedToposMorphism R S) [e.inverse.IsEquivalence] [IsIso e.ringMap]
    (e' : RingedToposMorphism (restrictRing F R) (restrictRing G S))
    [e'.inverse.IsEquivalence] [IsIso e'.ringMap]
    (q : e.inverse ⋙ restrictSets (J' := J') F ≅ restrictSets (J' := K') G ⋙ e'.inverse)
    (hr : q.hom.app (ringSets S) ≫ e'.ringMap = (restrictSets (J' := J') F).map e.ringMap)
    (W : ringedSiteModules.{u} S ≌ ringedSiteModules.{u} R) (p : W.inverse ≅ e.modules)
    (W' : ringedSiteModules.{u} (restrictRing G S) ≌
      ringedSiteModules.{u} (restrictRing (J' := J') F R)) (p' : W'.inverse ≅ e'.modules) :
    W.functor ⋙ restrictModules (J' := J') F R ≅ restrictModules (J' := K') G S ⋙ W'.functor := by
  let z := moduleSquareSets F G e e' q W p W' p'
  let d := inverseModulesIso e W p
  let t := inverseModulesIso e' W' p'
  have ha (M : ringedSiteModules.{u} S) :
      moduleAdd ((restrictModules (J' := J') F R).obj (W.functor.obj M)) ≫ z.hom.app M =
        (z.hom.app M ⊗ₘ z.hom.app M) ≫
          moduleAdd (W'.functor.obj ((restrictModules (J' := K') G S).obj M)) := by
    have hd := congrArg (restrictSets (J' := J') F).map (inverseModulesIso_add e W p M)
    simp only [Functor.map_comp, restrict_lift] at hd
    have hh := compare_binary (e.inverse ⋙ restrictSets (J' := J') F)
      (restrictSets (J' := K') G ⋙ e'.inverse) q
      ((restrictSets (J' := J') F).mapIso (d.app M)) ((restrictSets (J' := J') F).mapIso (d.app M))
      ((restrictSets (J' := J') F).mapIso (d.app M))
      (t.app ((restrictModules (J' := K') G S).obj M))
      (t.app ((restrictModules (J' := K') G S).obj M))
      (t.app ((restrictModules (J' := K') G S).obj M))
      (moduleAdd M)
      ((restrictSets (J' := J') F).map (moduleAdd (W.functor.obj M)))
      (moduleAdd (W'.functor.obj ((restrictModules (J' := K') G S).obj M)))
      hd (by
        ext U x
        exact congrArg (fun f ↦ f.hom.app U x)
          (inverseModulesIso_add e' W' p' ((restrictModules (J' := K') G S).obj M)))
    simp only [z, moduleSquareSets_hom]
    ext U x
    exact congrArg (fun f ↦ f.hom.app U x) hh
  have hs (M : ringedSiteModules.{u} S) :
      moduleSMul ((restrictModules (J' := J') F R).obj (W.functor.obj M)) ≫ z.hom.app M =
        (𝟙 _ ⊗ₘ z.hom.app M) ≫
          moduleSMul (W'.functor.obj ((restrictModules (J' := K') G S).obj M)) := by
    have hd := congrArg (restrictSets (J' := J') F).map (inverseModulesIso_smul e W p M)
    simp only [Functor.map_comp, restrict_lift] at hd
    have ht := inverseModulesIso_smul e' W' p'
      ((restrictModules (J' := K') G S).obj M)
    have h := compare_binary (e.inverse ⋙ restrictSets (J' := J') F)
      (restrictSets (J' := K') G ⋙ e'.inverse) q
      ((restrictSets (J' := J') F).mapIso (asIso e.ringMap))
      ((restrictSets (J' := J') F).mapIso (d.app M))
      ((restrictSets (J' := J') F).mapIso (d.app M))
      (asIso e'.ringMap) (t.app ((restrictModules (J' := K') G S).obj M))
      (t.app ((restrictModules (J' := K') G S).obj M))
      (moduleSMul M)
      ((restrictSets (J' := J') F).map (moduleSMul (W.functor.obj M)))
      (moduleSMul (W'.functor.obj ((restrictModules (J' := K') G S).obj M)))
      hd (by
        ext U x
        exact congrArg (fun f ↦ f.hom.app U x) ht)
    have hc : (((restrictSets (J' := J') F).mapIso (asIso e.ringMap)).symm ≪≫
        q.app (ringSets S) ≪≫ asIso e'.ringMap).hom = 𝟙 _ := by
      simp only [Iso.trans_hom, Iso.symm_hom, Iso.app_hom, asIso_hom,
        Functor.mapIso_inv, hr]
      rw [← Functor.map_comp]
      change (restrictSets (J' := J') F).map
        ((asIso e.ringMap).inv ≫ (asIso e.ringMap).hom) =
          𝟙 ((restrictSets (J' := J') F).obj (ringSets R))
      rw [Iso.inv_hom_id, Functor.map_id]
    rw [hc] at h
    simp only [z, moduleSquareSets_hom]
    ext U x
    exact congrArg (fun f ↦ f.hom.app U x) h
  refine NatIso.ofComponents (fun M ↦ liftModuleIso (z.app M) ?_ ?_) ?_
  · intro U x y
    exact congrArg (fun f ↦ f.hom.app U (x, y)) (ha M)
  · intro U r x
    exact congrArg (fun f ↦ f.hom.app U (r, x)) (hs M)
  · intro M N f
    ext U x
    exact congrArg (fun h ↦ h.hom.app U x) (z.hom.naturality f)

attribute [irreducible] moduleSquare

-- The original existential binders h and k are retained verbatim.
end CategoryTheory
