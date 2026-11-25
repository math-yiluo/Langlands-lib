/-
Copyright (c) 2026 Anthropic. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.TensorProduct
public import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.SheafificationRestrictScalars
public import WeilConjectures.Algebra.Category.ModuleCat.ExtendScalarsPushout

/-! # Change of rings along a sectionwise pushout square of ring sheaves

For a square of sheaves of commutative rings `f : A ⟶ B`, `g : A ⟶ C'`, `p : B ⟶ D`,
`q : C' ⟶ D` which is a pushout on every section ring, and a sheaf of `C'`-modules `M`,
change of rings commutes with restriction of scalars:
`B ⊗_A Res_g M ≅ Res_p (D ⊗_{C'} M)` (`SheafOfModules.changeOfRingsBaseChangeIso`),
naturally in `M` (`SheafOfModules.changeOfRingsBaseChangeIso_hom_naturality`).
Source: Stacks Project, Tag 03EK.
-/

@[expose] public section

set_option synthInstance.maxSize 4096
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

universe a b r

open CategoryTheory

open scoped TensorProduct ChangeOfRings

namespace SheafOfModules


variable {C : Type a} [Category.{b} C] [EssentiallySmall.{r} C] {J : GrothendieckTopology C}
  [J.HasSheafCompose (forget₂ CommRingCat.{r} RingCat.{r})]
  [J.WEqualsLocallyBijective AddCommGrpCat.{r}] [HasWeakSheafify J AddCommGrpCat.{r}]
  {A B C' D : Sheaf J CommRingCat.{r}}
  (f : A ⟶ B) (g : A ⟶ C') (p : B ⟶ D) (q : C' ⟶ D)
  (h : ∀ U : Cᵒᵖ, IsPushout (f.hom.app U) (g.hom.app U) (p.hom.app U) (q.hom.app U))

/-- The sectionwise base-change comparison of change-of-rings presheaves along a
sectionwise pushout square. Source: Stacks Project, Tag 03EK. -/
noncomputable def changeOfRingsPresheafBaseChangeIso
    (M : SheafOfModules.{r} ((sheafCompose J (forget₂ CommRingCat.{r} RingCat.{r})).obj C')) :
    SheafOfModules.changeOfRingsPresheaf f
        ((SheafOfModules.restrictScalars
          ((sheafCompose J (forget₂ CommRingCat.{r} RingCat.{r})).map g)).obj M) ≅
      (PresheafOfModules.restrictScalars
        ((sheafCompose J (forget₂ CommRingCat.{r} RingCat.{r})).map p).hom).obj
        (SheafOfModules.changeOfRingsPresheaf q M) :=
  PresheafOfModules.isoMk
    (fun U ↦ (ModuleCat.exists_extendScalars_restrictScalars_iso_of_isPushout
      (f.hom.app U) (g.hom.app U) (p.hom.app U) (q.hom.app U) (h U) (M.val.obj U)).choose)
    (by
      intro U V v
      ext z
      induction z using TensorProduct.inductionOn with
      | add x y hx hy => simp only [map_add, hx, hy]
      | tmul b m =>
        have heU := (ModuleCat.exists_extendScalars_restrictScalars_iso_of_isPushout
          (f.hom.app U) (g.hom.app U) (p.hom.app U) (q.hom.app U) (h U)
            (M.val.obj U)).choose_spec
        have heV := (ModuleCat.exists_extendScalars_restrictScalars_iso_of_isPushout
          (f.hom.app V) (g.hom.app V) (p.hom.app V) (q.hom.app V) (h V)
            (M.val.obj V)).choose_spec
        have hs := (SheafOfModules.exists_changeOfRingsMap f
          ((SheafOfModules.restrictScalars
            ((sheafCompose J (forget₂ CommRingCat.{r} RingCat.{r})).map g)).obj M) v).choose_spec
              b m
        have ht := (SheafOfModules.exists_changeOfRingsMap q M v).choose_spec
          (p.hom.app U b) m
        have hp := ConcreteCategory.congr_hom (p.hom.naturality v) b
        refine (congrArg _ hs).trans ((heV _ _).trans ?_)
        refine (congrArg (fun d ↦ d ⊗ₜ[C'.obj.obj V, (q.hom.app V).hom]
          (show M.val.obj V from M.val.map v m)) hp).trans ?_
        exact ht.symm.trans (congrArg _ (heU b m).symm))

omit [EssentiallySmall.{r} C] in
/-- The presheaf base-change comparison on pure tensors: `b ⊗ m ↦ p b ⊗ m`. -/
theorem changeOfRingsPresheafBaseChangeIso_hom_tmul
    (M : SheafOfModules.{r} ((sheafCompose J (forget₂ CommRingCat.{r} RingCat.{r})).obj C'))
    (U : Cᵒᵖ) (b : B.obj.obj U) (m : M.val.obj U) :
    ((SheafOfModules.changeOfRingsPresheafBaseChangeIso f g p q h M).hom.app U)
        (b ⊗ₜ[A.obj.obj U, (f.hom.app U).hom] m) =
      p.hom.app U b ⊗ₜ[C'.obj.obj U, (q.hom.app U).hom] m :=
  (ModuleCat.exists_extendScalars_restrictScalars_iso_of_isPushout
    (f.hom.app U) (g.hom.app U) (p.hom.app U) (q.hom.app U) (h U) (M.val.obj U)).choose_spec b m

/-- Base change of change of rings along a sectionwise pushout square of ring sheaves:
`B ⊗_A Res_g M ≅ Res_p (D ⊗_{C'} M)`. Source: Stacks Project, Tag 03EK. -/
noncomputable def changeOfRingsBaseChangeIso
    (M : SheafOfModules.{r} ((sheafCompose J (forget₂ CommRingCat.{r} RingCat.{r})).obj C')) :
    SheafOfModules.changeOfRings f
        ((SheafOfModules.restrictScalars
          ((sheafCompose J (forget₂ CommRingCat.{r} RingCat.{r})).map g)).obj M) ≅
      (SheafOfModules.restrictScalars
        ((sheafCompose J (forget₂ CommRingCat.{r} RingCat.{r})).map p)).obj
        (SheafOfModules.changeOfRings q M) :=
  (PresheafOfModules.sheafification
      (𝟙 ((sheafCompose J (forget₂ CommRingCat.{r} RingCat.{r})).obj B).obj)).mapIso
      (SheafOfModules.changeOfRingsPresheafBaseChangeIso f g p q h M) ≪≫
    SheafOfModules.sheafificationRestrictScalarsIso
      ((sheafCompose J (forget₂ CommRingCat.{r} RingCat.{r})).map p)
      (SheafOfModules.changeOfRingsPresheaf q M)

omit [EssentiallySmall.{r} C] in
/-- The base-change comparison is natural in the module. -/
theorem changeOfRingsBaseChangeIso_hom_naturality
    {M N : SheafOfModules.{r} ((sheafCompose J (forget₂ CommRingCat.{r} RingCat.{r})).obj C')}
    (φ : M ⟶ N) :
    SheafOfModules.changeOfRingsHom f _
        ((SheafOfModules.restrictScalars
          ((sheafCompose J (forget₂ CommRingCat.{r} RingCat.{r})).map g)).map φ) ≫
      (SheafOfModules.changeOfRingsBaseChangeIso f g p q h N).hom =
    (SheafOfModules.changeOfRingsBaseChangeIso f g p q h M).hom ≫
      (SheafOfModules.restrictScalars
        ((sheafCompose J (forget₂ CommRingCat.{r} RingCat.{r})).map p)).map
        (SheafOfModules.changeOfRingsHom q M φ) := by
  simp only [SheafOfModules.changeOfRingsBaseChangeIso, Iso.trans_hom, Functor.mapIso_hom,
    SheafOfModules.changeOfRingsHom, Category.assoc]
  rw [← SheafOfModules.sheafificationRestrictScalarsIso_hom_naturality, ← Functor.map_comp_assoc,
    ← Functor.map_comp_assoc]
  congr 2
  ext U z
  induction z using TensorProduct.inductionOn with
  | add x y hx hy => simp only [map_add, hx, hy]
  | tmul b m =>
    simp only [PresheafOfModules.comp_app, ModuleCat.hom_comp, LinearMap.comp_apply]
    rw [SheafOfModules.changeOfRingsPresheafBaseChangeIso_hom_tmul]
    exact SheafOfModules.changeOfRingsPresheafBaseChangeIso_hom_tmul f g p q h N U b
      (φ.val.app U m)

end SheafOfModules
