/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import Mathlib.CategoryTheory.ObjectProperty.FullSubcategory
public import Mathlib.CategoryTheory.Whiskering
public import Mathlib.CategoryTheory.EqToHom
public import WeilConjectures.FourierTransform.FdIntegralScalarPresentationForward.AbstractDescent

/-! # Assembly of the forward coherence from the representative formula

Abstract bookkeeping: a comparison which is, on every object, the inverse of a derived
square followed by an ordinary-to-completed comparison, inherits the cocycle and unit
equations of the derived square and of the completed associator and unit.
-/

@[expose] public section
set_option autoImplicit false
open CategoryTheory

namespace WeilConjectures.FdIntegralScalarForward

universe v₁ v₂ v₃ v₄ v₅ v₆ u₁ u₂ u₃ u₄ u₅ u₆

variable {DE : Type u₁} {DL : Type u₂} {DM : Type u₃} {AE : Type u₄} {AL : Type u₅}
  {AM : Type u₆} [Category.{v₁} DE] [Category.{v₂} DL] [Category.{v₃} DM]
  [Category.{v₄} AE] [Category.{v₅} AL] [Category.{v₆} AM]

/-- Associativity of a comparison given by the representative formula. -/
theorem assoc_assembly
    (SE : ObjectProperty DE) (SL : ObjectProperty DL) (SM : ObjectProperty DM)
    (PE : ObjectProperty AE) (PL : ObjectProperty AL) (PM : ObjectProperty AM)
    (IE : SE.FullSubcategory ⥤ PE.FullSubcategory)
    (IL : SL.FullSubcategory ⥤ PL.FullSubcategory)
    (IM : SM.FullSubcategory ⥤ PM.FullSubcategory)
    (TE : DE ⥤ AE) (TL : DL ⥤ AL) (TM : DM ⥤ AM)
    (θE : IE ⋙ PE.ι ≅ SE.ι ⋙ TE) (θL : IL ⋙ PL.ι ≅ SL.ι ⋙ TL)
    (θM : IM ⋙ PM.ι ≅ SM.ι ⋙ TM)
    (Sh : DE ⥤ DL) (Sk : DL ⥤ DM) (Shk : DE ⥤ DM)
    (hSh : ∀ K, SL ((SE.ι ⋙ Sh).obj K)) (hSk : ∀ K, SM ((SL.ι ⋙ Sk).obj K))
    (hShk : ∀ K, SM ((SE.ι ⋙ Shk).obj K))
    (Xh : AE ⥤ AL) (Xk : AL ⥤ AM) (Xhk : AE ⥤ AM)
    (hXh : ∀ K, PL ((PE.ι ⋙ Xh).obj K)) (hXk : ∀ K, PM ((PL.ι ⋙ Xk).obj K))
    (hXhk : ∀ K, PM ((PE.ι ⋙ Xhk).obj K))
    (bh : IE ⋙ PL.lift (PE.ι ⋙ Xh) hXh ≅ SL.lift (SE.ι ⋙ Sh) hSh ⋙ IL)
    (bk : IL ⋙ PM.lift (PL.ι ⋙ Xk) hXk ≅ SM.lift (SL.ι ⋙ Sk) hSk ⋙ IM)
    (bhk : IE ⋙ PM.lift (PE.ι ⋙ Xhk) hXhk ≅ SM.lift (SE.ι ⋙ Shk) hShk ⋙ IM)
    (aU : SL.lift (SE.ι ⋙ Sh) hSh ⋙ SM.lift (SL.ι ⋙ Sk) hSk ≅ SM.lift (SE.ι ⋙ Shk) hShk)
    (aC : PL.lift (PE.ι ⋙ Xh) hXh ⋙ PM.lift (PL.ι ⋙ Xk) hXk ≅
      PM.lift (PE.ι ⋙ Xhk) hXhk)
    (A : Xh ⋙ Xk ≅ Xhk) (hA : ∀ X, (aC.hom.app X).hom = A.hom.app X.obj)
    (Oh : DE ⥤ DL) (Ok : DL ⥤ DM) (Ohk : DE ⥤ DM) (Oc : Oh ⋙ Ok ≅ Ohk)
    (eh : Oh ⋙ TL ≅ TE ⋙ Xh) (ek : Ok ⋙ TM ≅ TL ⋙ Xk) (ehk : Ohk ⋙ TM ≅ TE ⋙ Xhk)
    (ωh : SE.ι ⋙ Oh ≅ SE.ι ⋙ Sh) (ωk : SL.ι ⋙ Ok ≅ SL.ι ⋙ Sk)
    (ωhk : SE.ι ⋙ Ohk ≅ SE.ι ⋙ Shk)
    (Gh : ∀ K, (bh.hom.app K).hom ≫ θL.hom.app ((SL.lift (SE.ι ⋙ Sh) hSh).obj K) =
      Xh.map (θE.hom.app K) ≫ eh.inv.app K.obj ≫ TL.map (ωh.hom.app K))
    (Gk : ∀ K, (bk.hom.app K).hom ≫ θM.hom.app ((SM.lift (SL.ι ⋙ Sk) hSk).obj K) =
      Xk.map (θL.hom.app K) ≫ ek.inv.app K.obj ≫ TM.map (ωk.hom.app K))
    (Ghk : ∀ K, (bhk.hom.app K).hom ≫ θM.hom.app ((SM.lift (SE.ι ⋙ Shk) hShk).obj K) =
      Xhk.map (θE.hom.app K) ≫ ehk.inv.app K.obj ≫ TM.map (ωhk.hom.app K))
    (hU : ∀ K, (aU.hom.app K).hom = ωk.inv.app ((SL.lift (SE.ι ⋙ Sh) hSh).obj K) ≫
      Ok.map (ωh.inv.app K) ≫ Oc.hom.app K.obj ≫ ωhk.hom.app K)
    (hD : ∀ Y, TM.map (Oc.hom.app Y) ≫ ehk.hom.app Y =
      ek.hom.app (Oh.obj Y) ≫ Xk.map (eh.hom.app Y) ≫ A.hom.app (TE.obj Y))
    (K : SE.FullSubcategory) :
    (PM.lift (PL.ι ⋙ Xk) hXk).map (bh.hom.app K) ≫
        bk.hom.app ((SL.lift (SE.ι ⋙ Sh) hSh).obj K) ≫ IM.map (aU.hom.app K) =
      aC.hom.app (IE.obj K) ≫ bhk.hom.app K := by
  have hIM : ∀ {X Y : SM.FullSubcategory} (f : X ⟶ Y),
      (IM.map f).hom = θM.hom.app X ≫ TM.map f.hom ≫ θM.inv.app Y := by
    intro X Y f
    have := θM.hom.naturality f
    simp only [Functor.comp_map, ObjectProperty.ι_map] at this
    rw [← Category.assoc, ← this]
    simp
  apply ObjectProperty.hom_ext
  simp only [ObjectProperty.FullSubcategory.comp_hom]
  change Xk.map (bh.hom.app K).hom ≫ _ ≫ _ = _
  rw [hIM, hA, hU, (Iso.eq_comp_inv (θL.app _)).2 (Gh K),
    (Iso.eq_comp_inv (θM.app _)).2 (Gk _),
    (Iso.eq_comp_inv (θM.app _)).2 (Ghk K)]
  simp only [Iso.app_inv, Functor.map_comp, Category.assoc,
    Iso.inv_hom_id_app_assoc]
  have hD' := hD K.obj
  have hDi : Xk.map (eh.inv.app K.obj) ≫ ek.inv.app (Oh.obj K.obj) ≫
      TM.map (Oc.hom.app K.obj) = A.hom.app (TE.obj K.obj) ≫ ehk.inv.app K.obj := by
    rw [← cancel_mono (ehk.hom.app K.obj)]
    simp only [Category.assoc, Iso.inv_hom_id_app]
    rw [hD']
    simp only [← Functor.map_comp_assoc, Iso.inv_hom_id_app_assoc, Iso.inv_hom_id_app]
    simp
  have hek := ek.inv.naturality (ωh.hom.app K)
  simp only [Functor.comp_map] at hek
  have hAn := A.hom.naturality (θE.hom.app K)
  simp only [Functor.comp_map] at hAn
  rw [← Xk.map_comp_assoc (θL.inv.app _), Iso.inv_hom_id_app, Functor.map_id, Category.id_comp,
    ← TM.map_comp_assoc (ωk.hom.app _), Iso.hom_inv_id_app, Functor.map_id, Category.id_comp]
  erw [reassoc_of% hek]
  rw [← TM.map_comp_assoc (Ok.map (ωh.hom.app K)), ← Ok.map_comp, Iso.hom_inv_id_app,
    Functor.map_id, Functor.map_id, Category.id_comp]
  erw [reassoc_of% hDi]
  erw [reassoc_of% hAn]
  rfl

/-- The unit equation of a comparison given by the representative formula. -/
theorem unit_assembly
    (SE : ObjectProperty DE) (PE : ObjectProperty AE)
    (IE : SE.FullSubcategory ⥤ PE.FullSubcategory) (TE : DE ⥤ AE)
    (θE : IE ⋙ PE.ι ≅ SE.ι ⋙ TE)
    (Sr : DE ⥤ DE) (hSr : ∀ K, SE ((SE.ι ⋙ Sr).obj K))
    (Xr : AE ⥤ AE) (hXr : ∀ K, PE ((PE.ι ⋙ Xr).obj K))
    (br : IE ⋙ PE.lift (PE.ι ⋙ Xr) hXr ≅ SE.lift (SE.ι ⋙ Sr) hSr ⋙ IE)
    (uU : SE.lift (SE.ι ⋙ Sr) hSr ≅ 𝟭 _) (uC : PE.lift (PE.ι ⋙ Xr) hXr ≅ 𝟭 _)
    (Xu : Xr ≅ 𝟭 AE) (hC : ∀ X, (uC.hom.app X).hom = Xu.hom.app X.obj)
    (Or : DE ⥤ DE) (ou : ∀ Y, Or.obj Y ⟶ Y) (er : Or ⋙ TE ≅ TE ⋙ Xr)
    (ωr : SE.ι ⋙ Or ≅ SE.ι ⋙ Sr)
    (Gr : ∀ K, (br.hom.app K).hom ≫ θE.hom.app ((SE.lift (SE.ι ⋙ Sr) hSr).obj K) =
      Xr.map (θE.hom.app K) ≫ er.inv.app K.obj ≫ TE.map (ωr.hom.app K))
    (hU : ∀ K, (uU.hom.app K).hom = ωr.inv.app K ≫ ou K.obj)
    (hD : ∀ Y, er.inv.app Y ≫ TE.map (ou Y) = Xu.hom.app (TE.obj Y))
    (K : SE.FullSubcategory) :
    br.hom.app K ≫ IE.map (uU.hom.app K) = uC.hom.app (IE.obj K) := by
  have hIE : ∀ {X Y : SE.FullSubcategory} (f : X ⟶ Y),
      (IE.map f).hom = θE.hom.app X ≫ TE.map f.hom ≫ θE.inv.app Y := by
    intro X Y f
    have := θE.hom.naturality f
    simp only [Functor.comp_map, ObjectProperty.ι_map] at this
    rw [← Category.assoc, ← this]
    simp
  apply ObjectProperty.hom_ext
  simp only [ObjectProperty.FullSubcategory.comp_hom]
  rw [hIE, hC, hU, (Iso.eq_comp_inv (θE.app _)).2 (Gr K)]
  simp only [Iso.app_inv, Functor.map_comp, Category.assoc, Iso.inv_hom_id_app_assoc]
  rw [← TE.map_comp_assoc (ωr.hom.app K), Iso.hom_inv_id_app, Functor.map_id, Category.id_comp]
  erw [reassoc_of% (hD K.obj)]
  have hn := Xu.hom.naturality (θE.hom.app K)
  simp only [Functor.id_map] at hn
  erw [reassoc_of% hn]
  simp

/-- `assoc_assembly`, with the completed associator given through its normalization at the
composite inclusion and equality transports. -/
theorem assoc_assembly_of_spec
    (SE : ObjectProperty DE) (SL : ObjectProperty DL) (SM : ObjectProperty DM)
    (PE : ObjectProperty AE) (PL : ObjectProperty AL) (PM : ObjectProperty AM)
    (IE : SE.FullSubcategory ⥤ PE.FullSubcategory)
    (IL : SL.FullSubcategory ⥤ PL.FullSubcategory)
    (IM : SM.FullSubcategory ⥤ PM.FullSubcategory)
    (TE : DE ⥤ AE) (TL : DL ⥤ AL) (TM : DM ⥤ AM)
    (θE : IE ⋙ PE.ι ≅ SE.ι ⋙ TE) (θL : IL ⋙ PL.ι ≅ SL.ι ⋙ TL)
    (θM : IM ⋙ PM.ι ≅ SM.ι ⋙ TM)
    (Sh : DE ⥤ DL) (Sk : DL ⥤ DM) (Shk : DE ⥤ DM)
    (hSh : ∀ K, SL ((SE.ι ⋙ Sh).obj K)) (hSk : ∀ K, SM ((SL.ι ⋙ Sk).obj K))
    (hShk : ∀ K, SM ((SE.ι ⋙ Shk).obj K))
    (Xh : AE ⥤ AL) (Xk : AL ⥤ AM) (Xhk : AE ⥤ AM)
    (hXh : ∀ K, PL ((PE.ι ⋙ Xh).obj K)) (hXk : ∀ K, PM ((PL.ι ⋙ Xk).obj K))
    (hXhk : ∀ K, PM ((PE.ι ⋙ Xhk).obj K))
    (bh : IE ⋙ PL.lift (PE.ι ⋙ Xh) hXh ≅ SL.lift (SE.ι ⋙ Sh) hSh ⋙ IL)
    (bk : IL ⋙ PM.lift (PL.ι ⋙ Xk) hXk ≅ SM.lift (SL.ι ⋙ Sk) hSk ⋙ IM)
    (bhk : IE ⋙ PM.lift (PE.ι ⋙ Xhk) hXhk ≅ SM.lift (SE.ι ⋙ Shk) hShk ⋙ IM)
    (aU : SL.lift (SE.ι ⋙ Sh) hSh ⋙ SM.lift (SL.ι ⋙ Sk) hSk ≅ SM.lift (SE.ι ⋙ Shk) hShk)
    (aC : PL.lift (PE.ι ⋙ Xh) hXh ⋙ PM.lift (PL.ι ⋙ Xk) hXk ≅
      PM.lift (PE.ι ⋙ Xhk) hXhk)
    (A : Xh ⋙ Xk ≅ Xhk) (hA : ∀ X, (aC.hom.app X).hom = A.hom.app X.obj)
    (Oh : DE ⥤ DL) (Ok : DL ⥤ DM) (Ohk : DE ⥤ DM) (Oc : Oh ⋙ Ok ≅ Ohk)
    (eh : Oh ⋙ TL ≅ TE ⋙ Xh) (ek : Ok ⋙ TM ≅ TL ⋙ Xk) (ehk : Ohk ⋙ TM ≅ TE ⋙ Xhk)
    (ωh : SE.ι ⋙ Oh ≅ SE.ι ⋙ Sh) (ωk : SL.ι ⋙ Ok ≅ SL.ι ⋙ Sk)
    (ωhk : SE.ι ⋙ Ohk ≅ SE.ι ⋙ Shk)
    (Gh : ∀ K, (bh.hom.app K).hom ≫ θL.hom.app ((SL.lift (SE.ι ⋙ Sh) hSh).obj K) =
      Xh.map (θE.hom.app K) ≫ eh.inv.app K.obj ≫ TL.map (ωh.hom.app K))
    (Gk : ∀ K, (bk.hom.app K).hom ≫ θM.hom.app ((SM.lift (SL.ι ⋙ Sk) hSk).obj K) =
      Xk.map (θL.hom.app K) ≫ ek.inv.app K.obj ≫ TM.map (ωk.hom.app K))
    (Ghk : ∀ K, (bhk.hom.app K).hom ≫ θM.hom.app ((SM.lift (SE.ι ⋙ Shk) hShk).obj K) =
      Xhk.map (θE.hom.app K) ≫ ehk.inv.app K.obj ≫ TM.map (ωhk.hom.app K))
    (hD : ∀ Y, TM.map (Oc.hom.app Y) ≫ ehk.hom.app Y =
      ek.hom.app (Oh.obj Y) ≫ Xk.map (eh.hom.app Y) ≫ A.hom.app (TE.obj Y))
    (Shk0 : DE ⥤ DM) (hShk0 : ∀ K, SM ((SE.ι ⋙ Shk0).obj K)) (eS : Shk0 = Shk)
    (aU0 : SL.lift (SE.ι ⋙ Sh) hSh ⋙ SM.lift (SL.ι ⋙ Sk) hSk ≅
      SM.lift (SE.ι ⋙ Shk0) hShk0) (haU : aU ≍ aU0)
    (Ohk0 : DE ⥤ DM) (eO : Ohk0 = Ohk) (Oc0 : Oh ⋙ Ok ≅ Ohk0) (hOc : Oc ≍ Oc0)
    (ωhk0 : SE.ι ⋙ Ohk0 ≅ SE.ι ⋙ Shk0) (hω : ωhk ≍ ωhk0)
    (hU0 : ∀ K, (aU0.hom.app K).hom = ωk.inv.app ((SL.lift (SE.ι ⋙ Sh) hSh).obj K) ≫
      Ok.map (ωh.inv.app K) ≫ Oc0.hom.app K.obj ≫ ωhk0.hom.app K)
    (K : SE.FullSubcategory) :
    (PM.lift (PL.ι ⋙ Xk) hXk).map (bh.hom.app K) ≫
        bk.hom.app ((SL.lift (SE.ι ⋙ Sh) hSh).obj K) ≫ IM.map (aU.hom.app K) =
      aC.hom.app (IE.obj K) ≫ bhk.hom.app K := by
  subst eS eO
  cases haU
  cases hOc
  cases hω
  exact assoc_assembly SE SL SM PE PL PM IE IL IM TE TL TM θE θL θM Sh Sk Shk0 hSh hSk hShk
    Xh Xk Xhk hXh hXk hXhk bh bk bhk _ aC A hA Oh Ok Ohk0 _ eh ek ehk ωh ωk _ Gh Gk Ghk
    hU0 hD K

/-- `unit_assembly`, with the completed unit given through its normalization at the identity
inclusion and equality transports. -/
theorem unit_assembly_of_spec
    (SE : ObjectProperty DE) (PE : ObjectProperty AE)
    (IE : SE.FullSubcategory ⥤ PE.FullSubcategory) (TE : DE ⥤ AE)
    (θE : IE ⋙ PE.ι ≅ SE.ι ⋙ TE)
    (Sr : DE ⥤ DE) (hSr : ∀ K, SE ((SE.ι ⋙ Sr).obj K))
    (Xr : AE ⥤ AE) (hXr : ∀ K, PE ((PE.ι ⋙ Xr).obj K))
    (br : IE ⋙ PE.lift (PE.ι ⋙ Xr) hXr ≅ SE.lift (SE.ι ⋙ Sr) hSr ⋙ IE)
    (uU : SE.lift (SE.ι ⋙ Sr) hSr ≅ 𝟭 _) (uC : PE.lift (PE.ι ⋙ Xr) hXr ≅ 𝟭 _)
    (Xu : Xr ≅ 𝟭 AE) (hC : ∀ X, (uC.hom.app X).hom = Xu.hom.app X.obj)
    (Or : DE ⥤ DE) (er : Or ⋙ TE ≅ TE ⋙ Xr)
    (ωr : SE.ι ⋙ Or ≅ SE.ι ⋙ Sr)
    (Gr : ∀ K, (br.hom.app K).hom ≫ θE.hom.app ((SE.lift (SE.ι ⋙ Sr) hSr).obj K) =
      Xr.map (θE.hom.app K) ≫ er.inv.app K.obj ≫ TE.map (ωr.hom.app K))
    (Sr0 : DE ⥤ DE) (hSr0 : ∀ K, SE ((SE.ι ⋙ Sr0).obj K)) (eS : Sr0 = Sr)
    (uU0 : SE.lift (SE.ι ⋙ Sr0) hSr0 ≅ 𝟭 _) (haU : uU ≍ uU0)
    (Or0 : DE ⥤ DE) (eO : Or0 = Or) (ωr0 : SE.ι ⋙ Or0 ≅ SE.ι ⋙ Sr0) (hω : ωr ≍ ωr0)
    (ou0 : ∀ Y, Or0.obj Y ⟶ Y)
    (hU0 : ∀ K, (uU0.hom.app K).hom = ωr0.inv.app K ≫ ou0 K.obj)
    (hD : ∀ Y, er.inv.app Y ≫ TE.map (eqToHom (Functor.congr_obj eO.symm Y) ≫ ou0 Y) =
      Xu.hom.app (TE.obj Y))
    (K : SE.FullSubcategory) :
    br.hom.app K ≫ IE.map (uU.hom.app K) = uC.hom.app (IE.obj K) := by
  subst eS eO
  cases haU
  cases hω
  exact unit_assembly SE PE IE TE θE Sr0 hSr Xr hXr br _ uC Xu hC Or0 ou0 er _ Gr hU0
    (fun Y ↦ by simpa using hD Y) K

theorem cocycle_ext {C : Type*} [Category C] (Q : C ⥤ DE) [Q.EssSurj]
    (Oh : DE ⥤ DL) (Ok : DL ⥤ DM) (Ohk : DE ⥤ DM)
    (TE : DE ⥤ AE) (TL : DL ⥤ AL) (TM : DM ⥤ AM)
    (Xh : AE ⥤ AL) (Xk : AL ⥤ AM) (Xhk : AE ⥤ AM)
    (eh : Oh ⋙ TL ≅ TE ⋙ Xh) (ek : Ok ⋙ TM ≅ TL ⋙ Xk) (ehk : Ohk ⋙ TM ≅ TE ⋙ Xhk)
    (Oc : Oh ⋙ Ok ≅ Ohk) (A : Xh ⋙ Xk ≅ Xhk)
    (h : ∀ P, TM.map (Oc.hom.app (Q.obj P)) ≫ ehk.hom.app (Q.obj P) =
      ek.hom.app (Oh.obj (Q.obj P)) ≫ Xk.map (eh.hom.app (Q.obj P)) ≫
        A.hom.app (TE.obj (Q.obj P))) (Y : DE) :
    TM.map (Oc.hom.app Y) ≫ ehk.hom.app Y =
      ek.hom.app (Oh.obj Y) ≫ Xk.map (eh.hom.app Y) ≫ A.hom.app (TE.obj Y) := by
  let α : (Oh ⋙ Ok) ⋙ TM ⟶ TE ⋙ Xhk := Functor.whiskerRight Oc.hom TM ≫ ehk.hom
  let β : (Oh ⋙ Ok) ⋙ TM ⟶ TE ⋙ Xhk :=
    (Functor.associator _ _ _).hom ≫ Functor.whiskerLeft Oh ek.hom ≫
      (Functor.associator _ _ _).inv ≫ Functor.whiskerRight eh.hom Xk ≫
      (Functor.associator _ _ _).hom ≫ Functor.whiskerLeft TE A.hom
  have key : ∀ P, α.app (Q.obj P) = β.app (Q.obj P) := fun P ↦ by simpa [α, β] using h P
  let i := Q.objObjPreimageIso Y
  have hα := α.naturality i.hom
  have hβ := β.naturality i.hom
  rw [key] at hα
  have : α.app Y = β.app Y := by
    rw [← cancel_epi (((Oh ⋙ Ok) ⋙ TM).map i.hom), hα, hβ]
  simpa [α, β] using this

/-- `assoc_assembly_of_spec`, with the derived cocycle obtained on representatives. -/
theorem assoc_assembly_full
    (SE : ObjectProperty DE) (SL : ObjectProperty DL) (SM : ObjectProperty DM)
    (PE : ObjectProperty AE) (PL : ObjectProperty AL) (PM : ObjectProperty AM)
    (IE : SE.FullSubcategory ⥤ PE.FullSubcategory)
    (IL : SL.FullSubcategory ⥤ PL.FullSubcategory)
    (IM : SM.FullSubcategory ⥤ PM.FullSubcategory)
    (TE : DE ⥤ AE) (TL : DL ⥤ AL) (TM : DM ⥤ AM)
    (θE : IE ⋙ PE.ι ≅ SE.ι ⋙ TE) (θL : IL ⋙ PL.ι ≅ SL.ι ⋙ TL)
    (θM : IM ⋙ PM.ι ≅ SM.ι ⋙ TM)
    (Sh : DE ⥤ DL) (Sk : DL ⥤ DM) (Shk : DE ⥤ DM)
    (hSh : ∀ K, SL ((SE.ι ⋙ Sh).obj K)) (hSk : ∀ K, SM ((SL.ι ⋙ Sk).obj K))
    (hShk : ∀ K, SM ((SE.ι ⋙ Shk).obj K))
    (Xh : AE ⥤ AL) (Xk : AL ⥤ AM) (Xhk : AE ⥤ AM)
    (hXh : ∀ K, PL ((PE.ι ⋙ Xh).obj K)) (hXk : ∀ K, PM ((PL.ι ⋙ Xk).obj K))
    (hXhk : ∀ K, PM ((PE.ι ⋙ Xhk).obj K))
    (bh : IE ⋙ PL.lift (PE.ι ⋙ Xh) hXh ≅ SL.lift (SE.ι ⋙ Sh) hSh ⋙ IL)
    (bk : IL ⋙ PM.lift (PL.ι ⋙ Xk) hXk ≅ SM.lift (SL.ι ⋙ Sk) hSk ⋙ IM)
    (bhk : IE ⋙ PM.lift (PE.ι ⋙ Xhk) hXhk ≅ SM.lift (SE.ι ⋙ Shk) hShk ⋙ IM)
    (aU : SL.lift (SE.ι ⋙ Sh) hSh ⋙ SM.lift (SL.ι ⋙ Sk) hSk ≅ SM.lift (SE.ι ⋙ Shk) hShk)
    (aC : PL.lift (PE.ι ⋙ Xh) hXh ⋙ PM.lift (PL.ι ⋙ Xk) hXk ≅
      PM.lift (PE.ι ⋙ Xhk) hXhk)
    (A : Xh ⋙ Xk ≅ Xhk) (hA : ∀ X, (aC.hom.app X).hom = A.hom.app X.obj)
    (Oh : DE ⥤ DL) (Ok : DL ⥤ DM) (Ohk : DE ⥤ DM) (Oc : Oh ⋙ Ok ≅ Ohk)
    (eh : Oh ⋙ TL ≅ TE ⋙ Xh) (ek : Ok ⋙ TM ≅ TL ⋙ Xk) (ehk : Ohk ⋙ TM ≅ TE ⋙ Xhk)
    (ωh : SE.ι ⋙ Oh ≅ SE.ι ⋙ Sh) (ωk : SL.ι ⋙ Ok ≅ SL.ι ⋙ Sk)
    (ωhk : SE.ι ⋙ Ohk ≅ SE.ι ⋙ Shk)
    (Gh : ∀ K, (bh.hom.app K).hom ≫ θL.hom.app ((SL.lift (SE.ι ⋙ Sh) hSh).obj K) =
      Xh.map (θE.hom.app K) ≫ eh.inv.app K.obj ≫ TL.map (ωh.hom.app K))
    (Gk : ∀ K, (bk.hom.app K).hom ≫ θM.hom.app ((SM.lift (SL.ι ⋙ Sk) hSk).obj K) =
      Xk.map (θL.hom.app K) ≫ ek.inv.app K.obj ≫ TM.map (ωk.hom.app K))
    (Ghk : ∀ K, (bhk.hom.app K).hom ≫ θM.hom.app ((SM.lift (SE.ι ⋙ Shk) hShk).obj K) =
      Xhk.map (θE.hom.app K) ≫ ehk.inv.app K.obj ≫ TM.map (ωhk.hom.app K))
    (Shk0 : DE ⥤ DM) (hShk0 : ∀ K, SM ((SE.ι ⋙ Shk0).obj K)) (eS : Shk0 = Shk)
    (aU0 : SL.lift (SE.ι ⋙ Sh) hSh ⋙ SM.lift (SL.ι ⋙ Sk) hSk ≅
      SM.lift (SE.ι ⋙ Shk0) hShk0) (haU : aU ≍ aU0)
    (Ohk0 : DE ⥤ DM) (eO : Ohk0 = Ohk) (Oc0 : Oh ⋙ Ok ≅ Ohk0) (hOc0 : Oc ≍ Oc0)
    (ωhk0 : SE.ι ⋙ Ohk0 ≅ SE.ι ⋙ Shk0) (hω : ωhk ≍ ωhk0)
    (hU0 : ∀ K, (aU0.hom.app K).hom = ωk.inv.app ((SL.lift (SE.ι ⋙ Sh) hSh).obj K) ≫
      Ok.map (ωh.inv.app K) ≫ Oc0.hom.app K.obj ≫ ωhk0.hom.app K)
    {KE KL KM CE CL CM : Type*} [Category KE] [Category KL] [Category KM] [Category CE]
    [Category CL] [Category CM]
    (QE : KE ⥤ DE) (QL : KL ⥤ DL) (QM : KM ⥤ DM) [QE.EssSurj]
    (RE : CE ⥤ AE) (RL : CL ⥤ AL) (RM : CM ⥤ AM)
    (oh : KE ⥤ KL) (ok : KL ⥤ KM) (ohk : KE ⥤ KM)
    (tE : KE ⥤ CE) (tL : KL ⥤ CL) (tM : KM ⥤ CM)
    (xh : CE ⥤ CL) (xk : CL ⥤ CM) (xhk : CE ⥤ CM)
    (foh : QE ⋙ Oh ≅ oh ⋙ QL) (fok : QL ⋙ Ok ≅ ok ⋙ QM) (fohk : QE ⋙ Ohk ≅ ohk ⋙ QM)
    (ftE : QE ⋙ TE ≅ tE ⋙ RE) (ftL : QL ⋙ TL ≅ tL ⋙ RL) (ftM : QM ⋙ TM ≅ tM ⋙ RM)
    (εh : RE ⋙ Xh ⟶ xh ⋙ RL) (εk : RL ⋙ Xk ⟶ xk ⋙ RM) (εhk : RE ⋙ Xhk ⟶ xhk ⋙ RM)
    (ch : oh ⋙ tL ≅ tE ⋙ xh) (ck : ok ⋙ tM ≅ tL ⋙ xk) (chk : ohk ⋙ tM ≅ tE ⋙ xhk)
    (oc : oh ⋙ ok ≅ ohk) (xc : xh ⋙ xk ≅ xhk)
    (heh : ∀ P, eh.hom.app (QE.obj P) ≫ Xh.map (ftE.hom.app P) ≫ εh.app (tE.obj P) =
      TL.map (foh.hom.app P) ≫ ftL.hom.app (oh.obj P) ≫ RL.map (ch.hom.app P))
    (hek : ∀ P, ek.hom.app (QL.obj P) ≫ Xk.map (ftL.hom.app P) ≫ εk.app (tL.obj P) =
      TM.map (fok.hom.app P) ≫ ftM.hom.app (ok.obj P) ≫ RM.map (ck.hom.app P))
    (hehk : ∀ P, ehk.hom.app (QE.obj P) ≫ Xhk.map (ftE.hom.app P) ≫ εhk.app (tE.obj P) =
      TM.map (fohk.hom.app P) ≫ ftM.hom.app (ohk.obj P) ≫ RM.map (chk.hom.app P))
    (hOc : ∀ P, Oc.hom.app (QE.obj P) ≫ fohk.hom.app P =
      Ok.map (foh.hom.app P) ≫ fok.hom.app (oh.obj P) ≫ QM.map (oc.hom.app P))
    (hA' : ∀ P, A.hom.app (RE.obj P) ≫ εhk.app P =
      Xk.map (εh.app P) ≫ εk.app (xh.obj P) ≫ RM.map (xc.hom.app P))
    (hc : ∀ P, ck.hom.app (oh.obj P) ≫ xk.map (ch.hom.app P) ≫ xc.hom.app (tE.obj P) =
      tM.map (oc.hom.app P) ≫ chk.hom.app P)
    (hiso : ∀ P, IsIso (εhk.app (tE.obj P)))
    (K : SE.FullSubcategory) :
    (PM.lift (PL.ι ⋙ Xk) hXk).map (bh.hom.app K) ≫
        bk.hom.app ((SL.lift (SE.ι ⋙ Sh) hSh).obj K) ≫ IM.map (aU.hom.app K) =
      aC.hom.app (IE.obj K) ≫ bhk.hom.app K :=
  assoc_assembly_of_spec SE SL SM PE PL PM IE IL IM TE TL TM θE θL θM Sh Sk Shk hSh hSk hShk
    Xh Xk Xhk hXh hXk hXhk bh bk bhk aU aC A hA Oh Ok Ohk Oc eh ek ehk ωh ωk ωhk Gh Gk Ghk
    (cocycle_ext QE Oh Ok Ohk TE TL TM Xh Xk Xhk eh ek ehk Oc A (fun P ↦ by
      have := hiso P
      exact derived_cocycle QE QL QM RE RL RM oh ok ohk tE tL tM xh xk xhk Oh Ok Ohk TE TL TM
        Xh Xk Xhk foh fok fohk ftE ftL ftM εh εk εhk ch ck chk oc xc eh ek ehk Oc A heh hek hehk
        hOc hA' hc P))
    Shk0 hShk0 eS aU0 haU Ohk0 eO Oc0 hOc0 ωhk0 hω hU0 K

end WeilConjectures.FdIntegralScalarForward
