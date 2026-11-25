/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import Mathlib.CategoryTheory.ObjectProperty.FullSubcategory
public import Mathlib.CategoryTheory.Whiskering
public import Mathlib.CategoryTheory.EqToHom

/-! # The representative formula of a lifted comparison

Abstract bookkeeping: a comparison of full subcategories characterized on good representatives
by a lift equation is, on every object, the inverse of a derived square followed by an
ordinary-to-completed comparison. Every category, functor and comparison is a variable, so that
the statement can be instantiated at a goal with the goal's own instance terms.
-/

@[expose] public section
set_option autoImplicit false
open CategoryTheory

namespace WeilConjectures.FdIntegralScalarForward

universe v₁ v₂ v₃ v₄ v₅ v₆ v₇ v₈ u₁ u₂ u₃ u₄ u₅ u₆ u₇ u₈

/-- The representative formula of a comparison given by its lift equation on good
representatives. -/
theorem lift_generic
    {KE : Type u₁} {KL : Type u₂} {DE : Type u₃} {DL : Type u₄} {AE : Type u₅} {AL : Type u₆}
    {CE : Type u₇} {CL : Type u₈}
    [Category.{v₁} KE] [Category.{v₂} KL] [Category.{v₃} DE] [Category.{v₄} DL]
    [Category.{v₅} AE] [Category.{v₆} AL] [Category.{v₇} CE] [Category.{v₈} CL]
    (QE : KE ⥤ DE) (QL : KL ⥤ DL) (RE : CE ⥤ AE) (RL : CL ⥤ AL)
    (SE : ObjectProperty DE) (SL : ObjectProperty DL)
    (PE : ObjectProperty AE) (PL : ObjectProperty AL)
    (IE : SE.FullSubcategory ⥤ PE.FullSubcategory)
    (IL : SL.FullSubcategory ⥤ PL.FullSubcategory)
    (TE : DE ⥤ AE) (TL : DL ⥤ AL)
    (hIE : IE ⋙ PE.ι = SE.ι ⋙ TE) (hIL : IL ⋙ PL.ι = SL.ι ⋙ TL)
    (Sh : DE ⥤ DL) (hSh : ∀ K, SL ((SE.ι ⋙ Sh).obj K))
    (Xh : AE ⥤ AL) (hXh : ∀ K, PL ((PE.ι ⋙ Xh).obj K))
    (bh : IE ⋙ PL.lift (PE.ι ⋙ Xh) hXh ≅ SL.lift (SE.ι ⋙ Sh) hSh ⋙ IL)
    (Oh : DE ⥤ DL) (eh : Oh ⋙ TL ≅ TE ⋙ Xh) (ωh : SE.ι ⋙ Oh ≅ SE.ι ⋙ Sh)
    (Good : ObjectProperty KE) (scF : KE ⥤ KL)
    (cmp : (Good.ι ⋙ QE) ⋙ Sh ≅ Good.ι ⋙ scF ⋙ QL)
    (tE : KE ⥤ CE) (tL : KL ⥤ CL) (xh : CE ⥤ CL)
    (fE : QE ⋙ TE ≅ tE ⋙ RE) (fL : QL ⋙ TL ≅ tL ⋙ RL)
    (cnt : ∀ P, Xh.obj (RE.obj P) ⟶ RL.obj (xh.obj P))
    (compl : ∀ P, xh.obj (tE.obj P) ⟶ tL.obj (scF.obj P))
    (oh : KE ⥤ KL) (foh : QE ⋙ Oh ≅ oh ⋙ QL) (otc : oh ⋙ tL ≅ tE ⋙ xh) (χ : oh ⟶ scF)
    (heD : ∀ P, eh.hom.app (QE.obj P) ≫ Xh.map (fE.hom.app P) ≫ cnt (tE.obj P) =
      TL.map (foh.hom.app P) ≫ fL.hom.app (oh.obj P) ≫ RL.map (otc.hom.app P))
    (hotc : ∀ P, otc.hom.app P ≫ compl P = tL.map (χ.app P))
    (hω : ∀ (V : Good.FullSubcategory) (hV : SE (QE.obj V.obj)),
      ωh.hom.app ⟨QE.obj V.obj, hV⟩ ≫ cmp.hom.app V =
        foh.hom.app V.obj ≫ QL.map (χ.app V.obj))
    (hlift : ∀ (V : Good.FullSubcategory) (hV : SE (QE.obj V.obj)),
      HEq ((bh.hom.app ⟨QE.obj V.obj, hV⟩).hom ≫
        eqToHom (congrArg (fun F ↦ F.obj ((SL.lift (SE.ι ⋙ Sh) hSh).obj
          ⟨QE.obj V.obj, hV⟩)) hIL) ≫
        TL.map (cmp.hom.app V) ≫ fL.hom.app (scF.obj V.obj))
      (Xh.map (fE.hom.app V.obj) ≫ cnt (tE.obj V.obj) ≫ RL.map (compl V.obj)))
    (hgood : ∀ K : SE.FullSubcategory, ∃ (V : Good.FullSubcategory)
      (hV : SE (QE.obj V.obj)), Nonempty ((⟨QE.obj V.obj, hV⟩ : SE.FullSubcategory) ≅ K))
    (K : SE.FullSubcategory) :
    (bh.hom.app K).hom ≫ (eqToIso hIL).hom.app ((SL.lift (SE.ι ⋙ Sh) hSh).obj K) =
      Xh.map ((eqToIso hIE).hom.app K) ≫ eh.inv.app K.obj ≫ TL.map (ωh.hom.app K) := by
  let α : (IE ⋙ PE.ι) ⋙ Xh ⟶ (SE.ι ⋙ Sh) ⋙ TL :=
    Functor.whiskerRight bh.hom PL.ι ≫ (Functor.associator _ _ _).hom ≫
      Functor.whiskerLeft (SL.lift (SE.ι ⋙ Sh) hSh) (eqToIso hIL).hom
  let β : (IE ⋙ PE.ι) ⋙ Xh ⟶ (SE.ι ⋙ Sh) ⋙ TL :=
    Functor.whiskerRight (eqToIso hIE).hom Xh ≫ (Functor.associator _ _ _).hom ≫
      Functor.whiskerLeft SE.ι eh.inv ≫ (Functor.associator _ _ _).inv ≫
      Functor.whiskerRight ωh.hom TL
  have hα : ∀ K, α.app K =
      (bh.hom.app K).hom ≫ (eqToIso hIL).hom.app ((SL.lift (SE.ι ⋙ Sh) hSh).obj K) := by
    intro K
    simp [α]
  have hβ : ∀ K, β.app K =
      Xh.map ((eqToIso hIE).hom.app K) ≫ eh.inv.app K.obj ≫ TL.map (ωh.hom.app K) := by
    intro K
    simp [β]
  have key : ∀ (V : Good.FullSubcategory) (hV : SE (QE.obj V.obj)),
      α.app ⟨QE.obj V.obj, hV⟩ = β.app ⟨QE.obj V.obj, hV⟩ := by
    intro V hV
    rw [hα, hβ]
    have h1 := (conj_eqToHom_iff_heq _ _
      (congrArg Xh.obj (Functor.congr_obj hIE ⟨QE.obj V.obj, hV⟩)) rfl).2 (hlift V hV)
    rw [← cancel_mono (TL.map (cmp.hom.app V) ≫ fL.hom.app (scF.obj V.obj))]
    simp only [eqToIso.hom, eqToHom_app, eqToHom_refl, Category.comp_id, Category.assoc]
      at h1 ⊢
    rw [h1, ← eqToHom_map, ← TL.map_comp_assoc, hω V hV, TL.map_comp, Category.assoc]
    · have hn := fL.hom.naturality (χ.app V.obj)
      simp only [Functor.comp_map] at hn
      rw [hn, ← hotc, RL.map_comp, ← reassoc_of% (heD V.obj), Iso.inv_hom_id_app_assoc]
  obtain ⟨V, hV, ⟨a⟩⟩ := hgood K
  have hK : α.app K = β.app K := by
    rw [← cancel_epi (((IE ⋙ PE.ι) ⋙ Xh).map a.hom), α.naturality, β.naturality, key]
  rw [← hα, ← hβ, hK]

end WeilConjectures.FdIntegralScalarForward
