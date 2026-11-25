/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.CategoryTheory.InternalActionSite.InternalActionSiteBasic
public import WeilConjectures.CategoryTheory.SiteCoveringAxioms
public import Mathlib.CategoryTheory.Sites.PrecoverageToGrothendieck
public import Mathlib.CategoryTheory.Sites.SheafCohomology.Basic
public import WeilConjectures.CategoryTheory.RingedSiteModules
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.Abelian
public import Mathlib.Algebra.Category.ModuleCat.Presheaf.Sheafification
import Mathlib.CategoryTheory.Sites.PreservesSheafification
import Mathlib.CategoryTheory.Sites.LeftExact

/-!
# Equivariant module sheafification as a reflector

Source: Stacks Project, Modules on Sites, Tag 03CY, and Sites, Tags 00WH, 00WJ,
00YR; the agent-formulated internal-action extension supporting paragraph (3) of
main-20261015, sk-thm-sf-ctf-stability-direct-images
(blueprint: lem-sfb-equivariant-module-sheafification-reflector).
-/

@[expose] public section

set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits

namespace CategoryTheory.InternalActionSite

private abbrev setProd {D : Type u} [Category D] (P Q : D ⥤ Type u) : D ⥤ Type u where
  obj X := P.obj X × Q.obj X
  map f := ↾fun x ↦ (P.map f x.1, Q.map f x.2)

private def setProdMap {D : Type u} [Category D] {P Q P' Q' : D ⥤ Type u}
    (f : P ⟶ P') (g : Q ⟶ Q') : setProd P Q ⟶ setProd P' Q' where
  app X := ↾fun x ↦ (f.app X x.1, g.app X x.2)
  naturality X Y h := by
    apply ConcreteCategory.hom_ext
    intro x
    change (f.app Y (P.map h x.1), g.app Y (Q.map h x.2)) =
      (P'.map h (f.app X x.1), Q'.map h (g.app X x.2))
    exact _root_.Prod.ext (NatTrans.naturality_apply f h x.1)
      (NatTrans.naturality_apply g h x.2)

private def setFst {D : Type u} [Category D] (P Q : D ⥤ Type u) : setProd P Q ⟶ P where
  app _ := ↾_root_.Prod.fst
  naturality _ _ _ := rfl

private def setSnd {D : Type u} [Category D] (P Q : D ⥤ Type u) : setProd P Q ⟶ Q where
  app _ := ↾_root_.Prod.snd
  naturality _ _ _ := rfl

set_option backward.isDefEq.respectTransparency false in
private noncomputable def setProdIso {D : Type u} [Category D] (P Q : D ⥤ Type u) :
    setProd P Q ≅ P ⨯ Q where
  hom := prod.lift (setFst P Q) (setSnd P Q)
  inv :=
    { app := fun X ↦ ↾fun x ↦ ((prod.fst : P ⨯ Q ⟶ P).app X x, (prod.snd : P ⨯ Q ⟶ Q).app X x)
      naturality := by
        intro X Y f
        apply ConcreteCategory.hom_ext
        intro x
        change ((prod.fst : P ⨯ Q ⟶ P).app Y ((P ⨯ Q).map f x),
          (prod.snd : P ⨯ Q ⟶ Q).app Y ((P ⨯ Q).map f x)) = _
        exact _root_.Prod.ext (NatTrans.naturality_apply (prod.fst : P ⨯ Q ⟶ P) f x)
          (NatTrans.naturality_apply (prod.snd : P ⨯ Q ⟶ Q) f x) }
  hom_inv_id := by
    apply NatTrans.ext
    funext X
    apply ConcreteCategory.hom_ext
    intro x
    apply _root_.Prod.ext
    · exact ConcreteCategory.congr_hom (C := Type u) (FC := TypeCat.Fun) (CC := fun X ↦ X)
        (NatTrans.congr_app (prod.lift_fst (setFst P Q) (setSnd P Q)) X) x
    · exact ConcreteCategory.congr_hom (C := Type u) (FC := TypeCat.Fun) (CC := fun X ↦ X)
        (NatTrans.congr_app (prod.lift_snd (setFst P Q) (setSnd P Q)) X) x
  inv_hom_id := by
    apply prod.hom_ext
    · rw [Category.assoc, prod.lift_fst, Category.id_comp]
      rfl
    · rw [Category.assoc, prod.lift_snd, Category.id_comp]
      rfl

set_option backward.isDefEq.respectTransparency false in
private theorem setProd_W {C : Type u} [SmallCategory C] (J : GrothendieckTopology C)
    {P Q P' Q' : Cᵒᵖ ⥤ Type u} (f : P ⟶ P') (g : Q ⟶ Q')
    (hf : J.W f) (hg : J.W g) : J.W (setProdMap f g) := by
  let F := presheafToSheaf J (Type u)
  have : IsIso (F.map f) := (J.W_iff f).mp hf
  have : IsIso (F.map g) := (J.W_iff g).mp hg
  have he : setProdMap f g = (setProdIso P Q).hom ≫ prod.map f g ≫
      (setProdIso P' Q').inv := by
    apply (cancel_mono (setProdIso P' Q').hom).mp
    simp only [Category.assoc, Iso.inv_hom_id, Category.comp_id]
    apply prod.hom_ext <;> ext X x <;>
      simp [setProdIso, setProdMap, setFst, setSnd]
  rw [he, J.W_iff]
  have hp : IsIso (F.map (prod.map f g)) := by
    have h : F.map (prod.map f g) = prodComparison F P Q ≫
        prod.map (F.map f) (F.map g) ≫ inv (prodComparison F P' Q') := by
      rw [← Category.assoc, IsIso.eq_comp_inv, prodComparison_natural]
    rw [h]
    infer_instance
  simp only [Functor.map_comp]
  infer_instance

set_option backward.isDefEq.respectTransparency false in
private theorem locally_eq {C : Type u} [SmallCategory C] (J : GrothendieckTopology C)
    {P A B : Cᵒᵖ ⥤ Type u} (η : P ⟶ A) [Presheaf.IsLocallySurjective J η]
    (hB : Presheaf.IsSheaf J B) {X : Cᵒᵖ} (x : A.obj X) (s t : B.obj X)
    (h : ∀ (Y : Cᵒᵖ) (f : X ⟶ Y) (p : P.obj Y),
      η.app Y p = A.map f x → B.map f s = B.map f t) : s = t := by
  let T : J.Cover X.unop := ⟨Presheaf.imageSieve η x, Presheaf.imageSieve_mem J η x⟩
  have e : (↾fun _ : PUnit ↦ s) = (↾fun _ : PUnit ↦ t) :=
    hB.hom_ext T _ _ (fun I ↦ by
      ext z
      exact h _ I.f.op (Presheaf.localPreimage η x I.f I.hf)
        (Presheaf.app_localPreimage η x I.f I.hf))
  exact ConcreteCategory.congr_hom e PUnit.unit

set_option backward.isDefEq.respectTransparency false in
private noncomputable def moduleUnit {C : Type u} [SmallCategory C]
    {J : GrothendieckTopology C} (R : Sheaf J RingCat.{u})
    (P : PresheafOfModules.{u} R.obj) :
    P ⟶ ((PresheafOfModules.sheafification (𝟙 R.obj)).obj P).val :=
  (PresheafOfModules.sheafificationAdjunction (𝟙 R.obj)).unit.app P

set_option backward.isDefEq.respectTransparency false in
private noncomputable def extendAction {C : Type u} [SmallCategory C]
    (J : GrothendieckTopology C) (K : Cᵒᵖ ⥤ GrpCat.{u}) (R : Sheaf J RingCat.{u})
    (P : EquivariantPresheaf K R.obj) :
    setProd (K ⋙ forget GrpCat) (sheafify J P.val.presheaf ⋙ forget AddCommGrpCat) ⟶
      sheafify J P.val.presheaf ⋙ forget AddCommGrpCat := by
  let η := Functor.whiskerRight (toSheafify J P.val.presheaf) (forget AddCommGrpCat)
  have hη : J.W η := J.W_of_preservesSheafification (forget AddCommGrpCat)
    _ (J.W_toSheafify P.val.presheaf)
  let α : setProd (K ⋙ forget GrpCat) (P.val.presheaf ⋙ forget AddCommGrpCat) ⟶
      P.val.presheaf ⋙ forget AddCommGrpCat :=
    { app := fun X ↦ ↾fun x ↦ P.action.act X x.1 x.2
      naturality := by
        intro X Y f
        ext x
        exact (P.action.naturality f x.1 x.2).symm }
  exact ((setProd_W J (𝟙 (K ⋙ forget GrpCat)) η
    (ObjectProperty.isLocal_of_isIso _ _) hη).homEquiv _
      ((sheafCompose J (forget AddCommGrpCat)).obj
        ((presheafToSheaf J AddCommGrpCat).obj P.val.presheaf)).property).symm (α ≫ η)

set_option backward.isDefEq.respectTransparency false in
private theorem extendAction_unit {C : Type u} [SmallCategory C]
    (J : GrothendieckTopology C) (K : Cᵒᵖ ⥤ GrpCat.{u}) (R : Sheaf J RingCat.{u})
    (P : EquivariantPresheaf K R.obj) (X : Cᵒᵖ) (g : K.obj X) (p : P.val.obj X) :
    (extendAction J K R P).app X (g, (toSheafify J P.val.presheaf).app X p) =
      (toSheafify J P.val.presheaf).app X (P.action.act X g p) := by
  have e := Equiv.apply_symm_apply
    ((setProd_W J (𝟙 (K ⋙ forget GrpCat))
      (Functor.whiskerRight (toSheafify J P.val.presheaf) (forget AddCommGrpCat))
      (ObjectProperty.isLocal_of_isIso _ _)
      (J.W_of_preservesSheafification (forget AddCommGrpCat) _
        (J.W_toSheafify P.val.presheaf))).homEquiv _
      ((sheafCompose J (forget AddCommGrpCat)).obj
        ((presheafToSheaf J AddCommGrpCat).obj P.val.presheaf)).property)
    ({ app := fun Y ↦ ↾fun x ↦ P.action.act Y x.1 x.2
       naturality := by
         intro Y Z f
         ext x
         exact (P.action.naturality f x.1 x.2).symm } ≫
      Functor.whiskerRight (toSheafify J P.val.presheaf) (forget AddCommGrpCat))
  exact ConcreteCategory.congr_hom (C := Type u) (CC := fun X ↦ X)
    (NatTrans.congr_app e X) (g, p)

section ActionConstruction

variable {C : Type u} [SmallCategory C] (J : GrothendieckTopology C)
  (K : Cᵒᵖ ⥤ GrpCat.{u}) (R : Sheaf J RingCat.{u})
  (P : EquivariantPresheaf K R.obj)

set_option backward.isDefEq.respectTransparency false in
private noncomputable abbrev sharp := (PresheafOfModules.sheafification (𝟙 R.obj)).obj P.val

set_option backward.isDefEq.respectTransparency false in
private noncomputable abbrev beta (X : Cᵒᵖ) (g : K.obj X)
    (p : (sharp J K R P).val.obj X) : (sharp J K R P).val.obj X :=
  (extendAction J K R P).app X (g, p)

set_option backward.isDefEq.respectTransparency false in
private theorem beta_nat {X Y : Cᵒᵖ} (f : X ⟶ Y) (g : K.obj X)
    (p : (sharp J K R P).val.obj X) :
    (sharp J K R P).val.map f (beta J K R P X g p) =
      beta J K R P Y (K.map f g) ((sharp J K R P).val.map f p) :=
  (NatTrans.naturality_apply (D := Type u) (CD := fun X ↦ X)
    (extendAction J K R P) f (g, p)).symm

set_option backward.isDefEq.respectTransparency false in
private theorem beta_unit (X : Cᵒᵖ) (g : K.obj X) (p : P.val.obj X) :
    beta J K R P X g ((moduleUnit R P.val).app X p) =
      (moduleUnit R P.val).app X (P.action.act X g p) :=
  extendAction_unit J K R P X g p

set_option backward.isDefEq.respectTransparency false in
private theorem sharp_eq {B : SheafOfModules.{u} R} {X : Cᵒᵖ}
    (x : (sharp J K R P).val.obj X) (s t : B.val.obj X)
    (h : ∀ (Y : Cᵒᵖ) (f : X ⟶ Y) (p : P.val.obj Y),
      (moduleUnit R P.val).app Y p = (sharp J K R P).val.map f x →
      B.val.map f s = B.val.map f t) : s = t := by
  exact locally_eq J
    (Functor.whiskerRight (toSheafify J P.val.presheaf) (forget AddCommGrpCat))
    ((sheafCompose J (forget AddCommGrpCat)).obj
      ((SheafOfModules.toSheaf R).obj B)).property x s t h

set_option backward.isDefEq.respectTransparency false in
private theorem beta_one (X : Cᵒᵖ) (p : (sharp J K R P).val.obj X) :
    beta J K R P X 1 p = p := by
  apply sharp_eq J K R P (B := sharp J K R P) p _ _
  intro Y f q hq
  rw [beta_nat, ← hq, beta_unit, map_one, map_one]
  rfl

set_option backward.isDefEq.respectTransparency false in
private theorem beta_mul (X : Cᵒᵖ) (g h : K.obj X)
    (p : (sharp J K R P).val.obj X) :
    beta J K R P X (g * h) p = beta J K R P X g (beta J K R P X h p) := by
  apply sharp_eq J K R P (B := sharp J K R P) p _ _
  intro Y f q hq
  rw [beta_nat, beta_nat, beta_nat, ← hq, beta_unit, beta_unit, beta_unit, map_mul, map_mul]
  rfl

set_option backward.isDefEq.respectTransparency false in
private theorem beta_add (X : Cᵒᵖ) (g : K.obj X)
    (p q : (sharp J K R P).val.obj X) :
    beta J K R P X g (p + q) = beta J K R P X g p + beta J K R P X g q := by
  apply sharp_eq J K R P (B := sharp J K R P) p _ _
  intro Y f p₀ hp
  rw [beta_nat, map_add, map_add, beta_nat, beta_nat, ← hp]
  apply sharp_eq J K R P (B := sharp J K R P) ((sharp J K R P).val.map f q) _ _
  intro Z k q₀ hq
  rw [beta_nat, map_add, map_add, beta_nat, beta_nat,
    ← PresheafOfModules.naturality_apply (moduleUnit R P.val) k p₀, ← hq,
    ← ((moduleUnit R P.val).app Z).hom.map_add, beta_unit, beta_unit, beta_unit,
    map_add, map_add]

set_option backward.isDefEq.respectTransparency false in
private theorem beta_smul (X : Cᵒᵖ) (g : K.obj X) (r : R.obj.obj X)
    (p : (sharp J K R P).val.obj X) :
    beta J K R P X g (r • p) = r • beta J K R P X g p := by
  apply sharp_eq J K R P (B := sharp J K R P) p _ _
  intro Y f p₀ hp
  rw [beta_nat, (sharp J K R P).val.map_smul,
    (sharp J K R P).val.map_smul, beta_nat, ← hp,
    ← ((moduleUnit R P.val).app Y).hom.map_smul, beta_unit, beta_unit, map_smul,
    ((moduleUnit R P.val).app Y).hom.map_smul]

set_option backward.isDefEq.respectTransparency false in
private noncomputable def sharpAction : LinearAction K (sharp J K R P).val where
  act X :=
    { toFun := fun g ↦
        { toFun := beta J K R P X g
          map_add' := beta_add J K R P X g
          map_smul' := beta_smul J K R P X g }
      map_one' := by ext p; exact beta_one J K R P X p
      map_mul' := by intro g h; ext p; exact beta_mul J K R P X g h p }
  naturality := beta_nat J K R P

set_option backward.isDefEq.respectTransparency false in
private theorem sharpAction_unique
    (b : ∀ X : Cᵒᵖ, K.obj X →* Function.End ((sharp J K R P).val.obj X))
    (hb : ∀ (X Y : Cᵒᵖ) (f : X ⟶ Y) (g : K.obj X) (p : (sharp J K R P).val.obj X),
      (sharp J K R P).val.map f (b X g p) =
        b Y (K.map f g) ((sharp J K R P).val.map f p))
    (hu : ∀ (X : Cᵒᵖ) (g : K.obj X) (p : P.val.obj X),
      (moduleUnit R P.val).app X (P.action.act X g p) =
        b X g ((moduleUnit R P.val).app X p))
    (X : Cᵒᵖ) (g : K.obj X) (p : (sharp J K R P).val.obj X) :
    b X g p = (sharpAction J K R P).act X g p := by
  change b X g p = beta J K R P X g p
  apply sharp_eq J K R P (B := sharp J K R P) p _ _
  intro Y f q hq
  rw [hb, beta_nat, ← hq, ← hu, beta_unit]

set_option backward.isDefEq.respectTransparency false in
private theorem sharpHom_equivariant
    (Q : EquivariantSheaf (K := K) J R) (v : P ⟶ Q.obj)
    (w : sharp J K R P ⟶ (forgetSheaf J R).obj Q)
    (hw : toSheafify J P.val.presheaf ≫ (PresheafOfModules.toPresheaf R.obj).map w.val =
      (PresheafOfModules.toPresheaf R.obj).map v.val)
    (X : Cᵒᵖ) (g : K.obj X) (p : (sharp J K R P).val.obj X) :
    w.val.app X ((sharpAction J K R P).act X g p) =
      Q.obj.action.act X g (w.val.app X p) := by
  change w.val.app X (beta J K R P X g p) = _
  apply sharp_eq J K R P (B := (forgetSheaf J R).obj Q) p _ _
  intro Y f q hq
  have wn (z : (sharp J K R P).val.obj X) :
      Q.obj.val.map f (w.val.app X z) =
        w.val.app Y ((sharp J K R P).val.map f z) :=
    (PresheafOfModules.naturality_apply w.val f z).symm
  change Q.obj.val.map f (w.val.app X (beta J K R P X g p)) =
    Q.obj.val.map f (Q.obj.action.act X g (w.val.app X p))
  rw [wn, beta_nat, Q.obj.action.naturality, wn, ← hq, beta_unit]
  have he (z : P.val.obj Y) :
      w.val.app Y ((moduleUnit R P.val).app Y z) = v.val.app Y z :=
    ConcreteCategory.congr_hom (NatTrans.congr_app hw Y) z
  rw [he, he]
  exact v.property Y (K.map f g) q

set_option backward.isDefEq.respectTransparency false in
private theorem sharpHom_exists (Q : EquivariantSheaf (K := K) J R) (v : P ⟶ Q.obj) :
    ∃! w : sharp J K R P ⟶ (forgetSheaf J R).obj Q,
      (∀ (X : Cᵒᵖ) (g : K.obj X) (p : (sharp J K R P).val.obj X),
        w.val.app X ((sharpAction J K R P).act X g p) =
          Q.obj.action.act X g (w.val.app X p)) ∧
      toSheafify J P.val.presheaf ≫ (PresheafOfModules.toPresheaf R.obj).map w.val =
        (PresheafOfModules.toPresheaf R.obj).map v.val := by
  let e := PresheafOfModules.sheafificationHomEquiv (𝟙 R.obj)
    (P := P.val) (F := (forgetSheaf J R).obj Q)
  let w := e.symm v.val
  have hw : toSheafify J P.val.presheaf ≫ (PresheafOfModules.toPresheaf R.obj).map w.val =
      (PresheafOfModules.toPresheaf R.obj).map v.val :=
    (PresheafOfModules.toPresheaf R.obj).congr_map (e.apply_symm_apply v.val)
  refine ⟨w, ⟨sharpHom_equivariant J K R P Q v w hw, hw⟩, ?_⟩
  intro z hz
  apply e.injective
  apply (PresheafOfModules.toPresheaf R.obj).map_injective
  exact hz.2.trans hw.symm

set_option backward.isDefEq.respectTransparency false in
private noncomputable def sharpObject : EquivariantSheaf (K := K) J R :=
  ⟨⟨(sharp J K R P).val, sharpAction J K R P⟩, (sharp J K R P).isSheaf⟩

set_option backward.isDefEq.respectTransparency false in
private noncomputable def sharpUnit : P ⟶ (sharpObject J K R P).obj :=
  ⟨moduleUnit R P.val, fun X g p ↦ (beta_unit J K R P X g p).symm⟩

set_option backward.isDefEq.respectTransparency false in
private theorem sharpUnit_universal (Q : EquivariantSheaf (K := K) J R) (v : P ⟶ Q.obj) :
    ∃! w : sharpObject J K R P ⟶ Q,
      sharpUnit J K R P ≫ (inclusion J R).map w = v := by
  obtain ⟨w, hw, huw⟩ := sharpHom_exists J K R P Q v
  refine ⟨⟨⟨w.val, hw.1⟩⟩, ?_, ?_⟩
  · apply Subtype.ext
    apply (PresheafOfModules.toPresheaf R.obj).map_injective
    exact hw.2
  · intro z hz
    have he : (⟨z.hom.val⟩ : sharp J K R P ⟶ (forgetSheaf J R).obj Q) = w := by
      apply huw
      refine ⟨z.hom.property, ?_⟩
      exact (PresheafOfModules.toPresheaf R.obj).congr_map (congrArg Subtype.val hz)
    apply ObjectProperty.hom_ext
    apply Subtype.ext
    exact congrArg SheafOfModules.Hom.val he

set_option backward.isDefEq.respectTransparency false in
private noncomputable def sharpEquiv (Q : EquivariantSheaf (K := K) J R) :
    (sharpObject J K R P ⟶ Q) ≃ (P ⟶ Q.obj) :=
  Equiv.ofBijective (fun w ↦ sharpUnit J K R P ≫ (inclusion J R).map w)
    ⟨fun f g h ↦ by
        obtain ⟨w, hw, huw⟩ := sharpUnit_universal J K R P Q
          (sharpUnit J K R P ≫ (inclusion J R).map f)
        exact (huw f rfl).trans (huw g h.symm).symm,
      fun v ↦ by
        obtain ⟨w, hw, _⟩ := sharpUnit_universal J K R P Q v
        exact ⟨w, hw⟩⟩

set_option backward.isDefEq.respectTransparency false in
private theorem sharpEquiv_natural (Q Q' : EquivariantSheaf (K := K) J R)
    (g : Q ⟶ Q') (h : sharpObject J K R P ⟶ Q) :
    sharpEquiv J K R P Q' (h ≫ g) =
      sharpEquiv J K R P Q h ≫ (inclusion J R).map g := by
  change sharpUnit J K R P ≫ (inclusion J R).map (h ≫ g) = _
  rw [Functor.map_comp, ← Category.assoc]
  rfl

set_option backward.isDefEq.respectTransparency false in
private noncomputable def sharpFunctor : EquivariantPresheaf K R.obj ⥤
    EquivariantSheaf (K := K) J R :=
  Adjunction.leftAdjointOfEquiv (G := inclusion J R)
    (F_obj := sharpObject J K R) (fun P Q ↦ sharpEquiv J K R P Q)
    (fun P Q Q' g h ↦ sharpEquiv_natural J K R P Q Q' g h)

set_option backward.isDefEq.respectTransparency false in
private noncomputable def sharpAdjunction : sharpFunctor J K R ⊣ inclusion J R :=
  Adjunction.adjunctionOfEquivLeft (G := inclusion J R)
    (F_obj := sharpObject J K R) (fun P Q ↦ sharpEquiv J K R P Q)
    (fun P Q Q' g h ↦ sharpEquiv_natural J K R P Q Q' g h)

set_option backward.isDefEq.respectTransparency false in
private theorem sharpAdjunction_unit (P : EquivariantPresheaf K R.obj) :
    (sharpAdjunction J K R).unit.app P = sharpUnit J K R P := by
  change (sharpEquiv J K R P _ (𝟙 _)) = sharpUnit J K R P
  change sharpUnit J K R P ≫ (inclusion J R).map (𝟙 (sharpObject J K R P)) = _
  rw [Functor.map_id]
  exact Category.comp_id (sharpUnit J K R P)

set_option backward.isDefEq.respectTransparency false in
private noncomputable def sharpComparison :
    sharpFunctor J K R ⋙ forgetSheaf J R ≅
      forgetPresheaf ⋙ PresheafOfModules.sheafification (𝟙 R.obj) :=
  NatIso.ofComponents (fun _ ↦ Iso.refl _) (by
    intro P Q f
    simp only [Iso.refl_hom, Category.comp_id, Category.id_comp]
    apply SheafOfModules.Hom.ext
    apply (PresheafOfModules.toPresheaf R.obj).map_injective
    apply (J.W_toSheafify P.val.presheaf _ (sharp J K R Q).isSheaf).1
    have hu := (sharpAdjunction J K R).unit.naturality f
    rw [sharpAdjunction_unit, sharpAdjunction_unit] at hu
    change toSheafify J P.val.presheaf ≫
      (PresheafOfModules.toPresheaf R.obj).map
        (((sharpFunctor J K R).map f).hom.val) = _
    calc
      _ = (PresheafOfModules.toPresheaf R.obj).map f.val ≫
          toSheafify J Q.val.presheaf :=
        (PresheafOfModules.toPresheaf R.obj).congr_map (congrArg Subtype.val hu).symm
      _ = _ := toSheafify_naturality J _)

end ActionConstruction

/-- Ordinary module sheafification carries the unique natural linear action extending
the given action, has the equivariant universal property, and gives the reflector.

Source: Stacks Tags 03CY, 00WH, 00WJ and 00YR; agent-formulated equivariant extension
(blueprint: lem-sfb-equivariant-module-sheafification-reflector).

Proof:
1. By lem-pc-sites-module-sheafification-interface, the underlying abelian sheaf and
   unit are ordinary abelian sheafification. By lem-pc-sites-sheafification-underlying-sets
   the same holds after forgetting to sets. The universal property in
   def-weil-pbc-sheafification fixes the sheaves K and R. Finite-product preservation
   (situation-conventions) identifies products of their identities and
   the unit of P with the corresponding sheafification units. Hence maps from these
   product sheaves are determined after those units.
2. Extend the composite of the action K times P to P with the unit P to P-sharp
   uniquely across the product unit, by def-weil-pbc-sheafification. This gives the
   natural action map and its uniqueness among maps making the unit equivariant.
3. Check identity, multiplication, addition and scalar-linearity after the product
   units, using situation-conventions and
   def-weil-pbc-sheafification. They become the corresponding laws on P; its unit is
   linear by lem-pc-sites-module-sheafification-interface. The action fixes zero
   directly. The action by the inverse group section is inverse to the action by
   that section. Thus the maps give the displayed LinearAction, without assuming K
   abelian.
4. An equivariant map to a module sheaf has its unique ordinary linear extension
   by lem-pc-sites-module-sheafification-interface. Compare its two action composites
   after the product unit. They agree by the original equivariance; product-unit
   uniqueness from def-weil-pbc-sheafification and
   situation-conventions makes the extension equivariant. Ordinary
   uniqueness gives equivariant uniqueness.
5. Extend the composite of each presheaf map with the target unit. The uniqueness
   from lem-pc-sites-module-sheafification-interface gives identity and composition
   laws, and naturality of the extension bijections in both arguments. This gives
   the adjunction. Forgetting actions gives ordinary module sheafification on
   objects and maps; the comparison preserves the unit, naturally in P. -/
theorem equivariantModuleSheafification_reflector
    {C : Type u} [SmallCategory C] [HasFiniteLimits C]
    (J : GrothendieckTopology C) (K : Cᵒᵖ ⥤ GrpCat.{u})
    (hK : Presheaf.IsSheaf J (K ⋙ forget GrpCat.{u}))
    (S : Sheaf J CommRingCat.{u}) :
    (∀ P : EquivariantPresheaf K (baseRing J S).obj,
      ∃ a : LinearAction K
          ((PresheafOfModules.sheafification (𝟙 (baseRing J S).obj)).obj P.val).val,
        (∀ (X : Cᵒᵖ) (g : K.obj X) (p : P.val.obj X),
          (toSheafify J P.val.presheaf).app X (P.action.act X g p) =
            a.act X g ((toSheafify J P.val.presheaf).app X p)) ∧
        (∀ b : ∀ X : Cᵒᵖ, K.obj X →* Function.End
            (((PresheafOfModules.sheafification (𝟙 (baseRing J S).obj)).obj P.val).val.obj X),
          (∀ (X Y : Cᵒᵖ) (f : X ⟶ Y) (g : K.obj X)
              (p : ((PresheafOfModules.sheafification
                (𝟙 (baseRing J S).obj)).obj P.val).val.obj X),
            ((PresheafOfModules.sheafification (𝟙 (baseRing J S).obj)).obj P.val).val.map f
                (b X g p) = b Y (K.map f g)
                  (((PresheafOfModules.sheafification
                    (𝟙 (baseRing J S).obj)).obj P.val).val.map f p)) →
          (∀ (X : Cᵒᵖ) (g : K.obj X) (p : P.val.obj X),
            (toSheafify J P.val.presheaf).app X (P.action.act X g p) =
              b X g ((toSheafify J P.val.presheaf).app X p)) →
          ∀ (X : Cᵒᵖ) (g : K.obj X)
              (p : ((PresheafOfModules.sheafification
                (𝟙 (baseRing J S).obj)).obj P.val).val.obj X),
            b X g p = a.act X g p) ∧
        (∀ (Q : EquivariantSheaf (K := K) J (baseRing J S)) (v : P ⟶ Q.obj),
          ∃! w : (PresheafOfModules.sheafification (𝟙 (baseRing J S).obj)).obj P.val ⟶
              (forgetSheaf J (baseRing J S)).obj Q,
            (∀ (X : Cᵒᵖ) (g : K.obj X)
                (p : ((PresheafOfModules.sheafification
                  (𝟙 (baseRing J S).obj)).obj P.val).val.obj X),
              w.val.app X (a.act X g p) = Q.obj.action.act X g (w.val.app X p)) ∧
            toSheafify J P.val.presheaf ≫
                (PresheafOfModules.toPresheaf (baseRing J S).obj).map w.val =
              (PresheafOfModules.toPresheaf (baseRing J S).obj).map v.val)) ∧
    (∃ F : EquivariantPresheaf K (baseRing J S).obj ⥤
        EquivariantSheaf (K := K) J (baseRing J S),
      ∃ adj : F ⊣ inclusion J (baseRing J S),
        ∃ comparison : F ⋙ forgetSheaf J (baseRing J S) ≅
            forgetPresheaf ⋙ PresheafOfModules.sheafification (𝟙 (baseRing J S).obj),
          ∀ P : EquivariantPresheaf K (baseRing J S).obj,
            (PresheafOfModules.toPresheaf (baseRing J S).obj).map
                (forgetPresheaf.map (adj.unit.app P)) ≫
              ((SheafOfModules.toSheaf (baseRing J S)).map
                (comparison.hom.app P)).hom = toSheafify J P.val.presheaf) := by
  have _hK := hK
  constructor
  · intro P
    exact ⟨sharpAction J K (baseRing J S) P,
      fun X g p ↦ (beta_unit J K (baseRing J S) P X g p).symm,
      sharpAction_unique J K (baseRing J S) P,
      sharpHom_exists J K (baseRing J S) P⟩
  · refine ⟨sharpFunctor J K (baseRing J S), sharpAdjunction J K (baseRing J S),
      sharpComparison J K (baseRing J S), ?_⟩
    intro P
    rw [sharpAdjunction_unit]
    change toSheafify J P.val.presheaf ≫ 𝟙 _ = _
    exact Category.comp_id _

end CategoryTheory.InternalActionSite
