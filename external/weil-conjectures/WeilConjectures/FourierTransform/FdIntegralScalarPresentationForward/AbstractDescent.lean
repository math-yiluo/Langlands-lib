/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import Mathlib.CategoryTheory.Iso
public import Mathlib.CategoryTheory.Functor.Category
public import Mathlib.CategoryTheory.Whiskering

/-! # Descent of coherence through normalized localization comparisons

Abstract categorical bookkeeping: comparisons between functors on localized categories
which are normalized on representatives by chain-level comparisons inherit the chain-level
cocycle and unit equations.
-/

@[expose] public section
set_option autoImplicit false
open CategoryTheory

namespace WeilConjectures.FdIntegralScalarForward

universe v₁ v₂ v₃ v₄ v₅ v₆ v₇ v₈ v₉ v₁₀ v₁₁ v₁₂ u₁ u₂ u₃ u₄ u₅ u₆ u₇ u₈ u₉ u₁₀ u₁₁ u₁₂

/-- Normalized comparisons inherit the chain-level cocycle, checked on a representative. -/
theorem derived_cocycle
    {KE : Type u₁} {KL : Type u₂} {KM : Type u₃} {PE : Type u₄} {PL : Type u₅} {PM : Type u₆}
    {DE : Type u₇} {DL : Type u₈} {DM : Type u₉} {EE : Type u₁₀} {EL : Type u₁₁}
    {EM : Type u₁₂}
    [Category.{v₁} KE] [Category.{v₂} KL] [Category.{v₃} KM] [Category.{v₄} PE]
    [Category.{v₅} PL] [Category.{v₆} PM] [Category.{v₇} DE] [Category.{v₈} DL]
    [Category.{v₉} DM] [Category.{v₁₀} EE] [Category.{v₁₁} EL] [Category.{v₁₂} EM]
    (QE : KE ⥤ DE) (QL : KL ⥤ DL) (QM : KM ⥤ DM)
    (RE : PE ⥤ EE) (RL : PL ⥤ EL) (RM : PM ⥤ EM)
    (oh : KE ⥤ KL) (ok : KL ⥤ KM) (ohk : KE ⥤ KM)
    (tE : KE ⥤ PE) (tL : KL ⥤ PL) (tM : KM ⥤ PM)
    (xh : PE ⥤ PL) (xk : PL ⥤ PM) (xhk : PE ⥤ PM)
    (Oh : DE ⥤ DL) (Ok : DL ⥤ DM) (Ohk : DE ⥤ DM)
    (TE : DE ⥤ EE) (TL : DL ⥤ EL) (TM : DM ⥤ EM)
    (Xh : EE ⥤ EL) (Xk : EL ⥤ EM) (Xhk : EE ⥤ EM)
    (foh : QE ⋙ Oh ≅ oh ⋙ QL) (fok : QL ⋙ Ok ≅ ok ⋙ QM) (fohk : QE ⋙ Ohk ≅ ohk ⋙ QM)
    (ftE : QE ⋙ TE ≅ tE ⋙ RE) (ftL : QL ⋙ TL ≅ tL ⋙ RL) (ftM : QM ⋙ TM ≅ tM ⋙ RM)
    (εh : RE ⋙ Xh ⟶ xh ⋙ RL) (εk : RL ⋙ Xk ⟶ xk ⋙ RM) (εhk : RE ⋙ Xhk ⟶ xhk ⋙ RM)
    (ch : oh ⋙ tL ≅ tE ⋙ xh) (ck : ok ⋙ tM ≅ tL ⋙ xk) (chk : ohk ⋙ tM ≅ tE ⋙ xhk)
    (oc : oh ⋙ ok ≅ ohk) (xc : xh ⋙ xk ≅ xhk)
    (eh : Oh ⋙ TL ≅ TE ⋙ Xh) (ek : Ok ⋙ TM ≅ TL ⋙ Xk) (ehk : Ohk ⋙ TM ≅ TE ⋙ Xhk)
    (Oc : Oh ⋙ Ok ≅ Ohk) (A : Xh ⋙ Xk ≅ Xhk)
    (heh : ∀ P, eh.hom.app (QE.obj P) ≫ Xh.map (ftE.hom.app P) ≫ εh.app (tE.obj P) =
      TL.map (foh.hom.app P) ≫ ftL.hom.app (oh.obj P) ≫ RL.map (ch.hom.app P))
    (hek : ∀ P, ek.hom.app (QL.obj P) ≫ Xk.map (ftL.hom.app P) ≫ εk.app (tL.obj P) =
      TM.map (fok.hom.app P) ≫ ftM.hom.app (ok.obj P) ≫ RM.map (ck.hom.app P))
    (hehk : ∀ P, ehk.hom.app (QE.obj P) ≫ Xhk.map (ftE.hom.app P) ≫ εhk.app (tE.obj P) =
      TM.map (fohk.hom.app P) ≫ ftM.hom.app (ohk.obj P) ≫ RM.map (chk.hom.app P))
    (hOc : ∀ P, Oc.hom.app (QE.obj P) ≫ fohk.hom.app P =
      Ok.map (foh.hom.app P) ≫ fok.hom.app (oh.obj P) ≫ QM.map (oc.hom.app P))
    (hA : ∀ P, A.hom.app (RE.obj P) ≫ εhk.app P =
      Xk.map (εh.app P) ≫ εk.app (xh.obj P) ≫ RM.map (xc.hom.app P))
    (hc : ∀ P, ck.hom.app (oh.obj P) ≫ xk.map (ch.hom.app P) ≫ xc.hom.app (tE.obj P) =
      tM.map (oc.hom.app P) ≫ chk.hom.app P)
    (P : KE) [IsIso (εhk.app (tE.obj P))] :
    TM.map (Oc.hom.app (QE.obj P)) ≫ ehk.hom.app (QE.obj P) =
      ek.hom.app (Oh.obj (QE.obj P)) ≫ Xk.map (eh.hom.app (QE.obj P)) ≫
        A.hom.app (TE.obj (QE.obj P)) := by
  apply (cancel_mono (Xhk.map (ftE.hom.app P) ≫ εhk.app (tE.obj P))).1
  simp only [Category.assoc]
  rw [heh P |> fun _ ↦ hehk P]
  -- left side
  have hl : TM.map (Oc.hom.app (QE.obj P)) ≫ TM.map (fohk.hom.app P) =
      TM.map (Ok.map (foh.hom.app P)) ≫ TM.map (fok.hom.app (oh.obj P)) ≫
        TM.map (QM.map (oc.hom.app P)) := by
    rw [← TM.map_comp, hOc P, TM.map_comp, TM.map_comp]
  have hftM := ftM.hom.naturality (oc.hom.app P)
  simp only [Functor.comp_map] at hftM
  rw [reassoc_of% hl, reassoc_of% hftM]
  -- right side
  have hAn := A.hom.naturality (ftE.hom.app P)
  simp only [Functor.comp_map] at hAn
  rw [← reassoc_of% hAn, hA (tE.obj P)]
  have hεk := εk.naturality (ch.hom.app P)
  simp only [Functor.comp_map] at hεk
  have hXk : Xk.map (eh.hom.app (QE.obj P)) ≫ Xk.map (Xh.map (ftE.hom.app P)) ≫
      Xk.map (εh.app (tE.obj P)) =
      Xk.map (TL.map (foh.hom.app P)) ≫ Xk.map (ftL.hom.app (oh.obj P)) ≫
        Xk.map (RL.map (ch.hom.app P)) := by
    rw [← Xk.map_comp, ← Xk.map_comp, heh P, Xk.map_comp, Xk.map_comp]
  rw [reassoc_of% hXk, reassoc_of% hεk]
  have hekn := ek.hom.naturality (foh.hom.app P)
  simp only [Functor.comp_map] at hekn
  rw [reassoc_of% hekn.symm, reassoc_of% (hek (oh.obj P))]
  simp only [← RM.map_comp]
  rw [hc P]

/-- Normalized comparisons inherit the chain-level unit equation. -/
theorem derived_unit
    {KE : Type u₁} {PE : Type u₄} {DE : Type u₇} {EE : Type u₁₀}
    [Category.{v₁} KE] [Category.{v₄} PE] [Category.{v₇} DE] [Category.{v₁₀} EE]
    (QE : KE ⥤ DE) (RE : PE ⥤ EE) (oh : KE ⥤ KE) (tE : KE ⥤ PE) (xh : PE ⥤ PE)
    (Oh : DE ⥤ DE) (TE : DE ⥤ EE) (Xh : EE ⥤ EE)
    (foh : QE ⋙ Oh ≅ oh ⋙ QE) (ftE : QE ⋙ TE ≅ tE ⋙ RE) (εh : RE ⋙ Xh ⟶ xh ⋙ RE)
    (ch : oh ⋙ tE ≅ tE ⋙ xh) (ou : oh ≅ 𝟭 KE) (xu : xh ≅ 𝟭 PE)
    (eh : Oh ⋙ TE ≅ TE ⋙ Xh) (Ou : Oh ≅ 𝟭 DE) (Xu : Xh ≅ 𝟭 EE)
    (heh : ∀ P, eh.hom.app (QE.obj P) ≫ Xh.map (ftE.hom.app P) ≫ εh.app (tE.obj P) =
      TE.map (foh.hom.app P) ≫ ftE.hom.app (oh.obj P) ≫ RE.map (ch.hom.app P))
    (hOu : ∀ P, Ou.hom.app (QE.obj P) = foh.hom.app P ≫ QE.map (ou.hom.app P))
    (hXu : ∀ P, Xu.hom.app (RE.obj P) = εh.app P ≫ RE.map (xu.hom.app P))
    (hc : ∀ P, ch.inv.app P ≫ tE.map (ou.hom.app P) = xu.hom.app (tE.obj P))
    (P : KE) :
    eh.inv.app (QE.obj P) ≫ TE.map (Ou.hom.app (QE.obj P)) = Xu.hom.app (TE.obj (QE.obj P)) := by
  have key : TE.map (foh.hom.app P) ≫ ftE.hom.app (oh.obj P) =
      eh.hom.app (QE.obj P) ≫ Xh.map (ftE.hom.app P) ≫ εh.app (tE.obj P) ≫
        RE.map (ch.inv.app P) := by
    rw [reassoc_of% (heh P), ← RE.map_comp, Iso.hom_inv_id_app]
    erw [RE.map_id, Category.comp_id]
  have hXn := Xu.hom.naturality (ftE.hom.app P)
  simp only [Functor.id_map] at hXn
  have hft := ftE.hom.naturality (ou.hom.app P)
  simp only [Functor.comp_map] at hft
  apply (cancel_mono (ftE.hom.app P)).1
  erw [Category.assoc, ← hXn]
  rw [hOu P, TE.map_comp, Category.assoc]
  erw [hft]
  rw [reassoc_of% key]
  erw [hXu (tE.obj P)]
  simp only [Iso.inv_hom_id_app_assoc]
  rw [← RE.map_comp, hc P]

end WeilConjectures.FdIntegralScalarForward
