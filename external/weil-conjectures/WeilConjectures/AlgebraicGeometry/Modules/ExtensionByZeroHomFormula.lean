/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.CategoryTheory.ExtensionByZeroPresheaf
public import Mathlib.AlgebraicGeometry.Modules.Sheaf

/-! # A component of extension by zero for modules

## References

* Stacks Project, Sheaves, Lemma 00A7
* Stacks Project, Sheaves, Definition 00A4 and Lemma 00A7 (2)
-/

@[expose] public section

universe u

open CategoryTheory CategoryTheory.Limits Opposite

noncomputable section

namespace AlgebraicGeometry.Scheme.Modules

open SheafOfModules

-- The private Hom-equivalence construction below is adapted from
-- WeilConjectures.CategoryTheory.LocalizedModuleAdjunctionExact (group H1).
-- It implements Stacks Project Lemma 03DI and specializes to Lemma 00A7 here.
set_option backward.isDefEq.respectTransparency false in
set_option backward.defeqAttrib.useBackward true in
open Classical in
private noncomputable def extensionPresheafToHom
    {C : Type u} [SmallCategory C] {J : GrothendieckTopology C}
    (R : Sheaf J RingCat.{u}) (U : C)
    (F : SheafOfModules.{u} (R.over U)) (G : SheafOfModules.{u} R)
    (a : extensionByZeroPresheafObj R U F ⟶ G.val) :
    F ⟶ (overFunctor R U).obj G where
  val.app X := ModuleCat.ofHom
    ((a.app (Opposite.op X.unop.left)).hom.comp
      (DirectSum.lof (R.obj.obj (Opposite.op X.unop.left)) (X.unop.left ⟶ U)
        (fun φ ↦ F.val.obj (Opposite.op (Over.mk φ))) X.unop.hom))
  val.naturality {X Y} f := by
    ext x
    have h := PresheafOfModules.naturality_apply a
      ((Over.forget U).op.map f)
      (DirectSum.of _ X.unop.hom x)
    change a.app (Opposite.op Y.unop.left)
        (extensionByZeroPresheafRestrictAdd R U F ((Over.forget U).op.map f)
          (DirectSum.of _ X.unop.hom x)) = _ at h
    have restrict {V W : Cᵒᵖ} (a0 : V ⟶ W) (φ : V.unop ⟶ U)
        (ψ : W.unop ⟶ U) (hh : a0.unop ≫ φ = ψ)
        (z : F.val.obj (Opposite.op (Over.mk φ))) :
        extensionByZeroPresheafRestrictAdd R U F a0
            (DirectSum.of (fun q : V.unop ⟶ U ↦
              F.val.obj (Opposite.op (Over.mk q))) φ z) =
          DirectSum.of (fun q : W.unop ⟶ U ↦
            F.val.obj (Opposite.op (Over.mk q))) ψ
            (F.val.map (Opposite.op
              (Over.homMk a0.unop hh : Over.mk ψ ⟶ Over.mk φ)) z) := by
      subst ψ
      change (DirectSum.toAddMonoid _)
        (DirectSum.of (fun q : V.unop ⟶ U ↦
          F.val.obj (Opposite.op (Over.mk q))) φ z) = _
      rw [DirectSum.toAddMonoid_of]
      rfl
    have hr := restrict ((Over.forget U).op.map f) X.unop.hom Y.unop.hom
      (Over.w f.unop) x
    erw [hr] at h
    have hf : (Over.homMk f.unop.left (Over.w f.unop) : Y.unop ⟶ X.unop) =
        f.unop := by ext; rfl
    erw [hf] at h
    change a.app (Opposite.op Y.unop.left)
        (DirectSum.of (fun φ : Y.unop.left ⟶ U ↦
          F.val.obj (Opposite.op (Over.mk φ))) Y.unop.hom (F.val.map f x)) =
      G.val.map ((Over.forget U).op.map f)
        (a.app (Opposite.op X.unop.left)
          (DirectSum.of (fun φ : X.unop.left ⟶ U ↦
            F.val.obj (Opposite.op (Over.mk φ))) X.unop.hom x))
    exact h

set_option backward.isDefEq.respectTransparency false in
set_option backward.defeqAttrib.useBackward true in
open Classical in
private noncomputable def extensionHomToPresheaf
    {C : Type u} [SmallCategory C] {J : GrothendieckTopology C}
    (R : Sheaf J RingCat.{u}) (U : C)
    (F : SheafOfModules.{u} (R.over U)) (G : SheafOfModules.{u} R)
    (a : F ⟶ (overFunctor R U).obj G) :
    extensionByZeroPresheafObj R U F ⟶ G.val where
  app V := ModuleCat.ofHom (DirectSum.toModule _ _ _
    (fun φ : V.unop ⟶ U ↦ (a.val.app (Opposite.op (Over.mk φ))).hom))
  naturality {V W} f := by
    ext x
    induction x using DirectSum.induction_on with
    | zero => simp
    | of φ x =>
      change (DirectSum.toModule (R.obj.obj W) _ (G.val.obj W)
        (fun ψ : W.unop ⟶ U ↦ (a.val.app (Opposite.op (Over.mk ψ))).hom))
        (extensionByZeroPresheafRestrictAdd R U F f
          (DirectSum.of (fun ψ : V.unop ⟶ U ↦ F.val.obj (Opposite.op (Over.mk ψ))) φ x)) =
          G.val.map f ((DirectSum.toModule (R.obj.obj V) _ (G.val.obj V)
            (fun ψ : V.unop ⟶ U ↦ (a.val.app (Opposite.op (Over.mk ψ))).hom))
            (DirectSum.of (fun ψ : V.unop ⟶ U ↦ F.val.obj (Opposite.op (Over.mk ψ))) φ x))
      have restrict {V W : Cᵒᵖ} (a0 : V ⟶ W) (φ : V.unop ⟶ U)
          (ψ : W.unop ⟶ U) (hh : a0.unop ≫ φ = ψ)
          (z : F.val.obj (Opposite.op (Over.mk φ))) :
          extensionByZeroPresheafRestrictAdd R U F a0
              (DirectSum.of (fun q : V.unop ⟶ U ↦
                F.val.obj (Opposite.op (Over.mk q))) φ z) =
            DirectSum.of (fun q : W.unop ⟶ U ↦
              F.val.obj (Opposite.op (Over.mk q))) ψ
              (F.val.map (Opposite.op
                (Over.homMk a0.unop hh : Over.mk ψ ⟶ Over.mk φ)) z) := by
        subst ψ
        change (DirectSum.toAddMonoid _)
          (DirectSum.of (fun q : V.unop ⟶ U ↦
            F.val.obj (Opposite.op (Over.mk q))) φ z) = _
        rw [DirectSum.toAddMonoid_of]
        rfl
      have hr := restrict f φ (f.unop ≫ φ) rfl x
      erw [hr]
      erw [DirectSum.toModule_lof, DirectSum.toModule_lof]
      exact PresheafOfModules.naturality_apply a.val
        (Opposite.op (Over.homMk f.unop : Over.mk (f.unop ≫ φ) ⟶ Over.mk φ)) x
    | add x y hx hy => simpa only [map_add] using congrArg₂ (· + ·) hx hy

set_option backward.isDefEq.respectTransparency false in
open Classical in
private noncomputable def extensionPresheafHomEquiv
    {C : Type u} [SmallCategory C] {J : GrothendieckTopology C}
    (R : Sheaf J RingCat.{u}) (U : C)
    (F : SheafOfModules.{u} (R.over U)) (G : SheafOfModules.{u} R) :
    (extensionByZeroPresheafObj R U F ⟶ G.val) ≃
      (F ⟶ (overFunctor R U).obj G) where
  toFun := extensionPresheafToHom R U F G
  invFun := extensionHomToPresheaf R U F G
  left_inv a := by
    ext V x
    change (DirectSum.toModule (R.obj.obj V) _ (G.val.obj V)
      (fun φ : V.unop ⟶ U ↦ (a.app V).hom.comp
        (DirectSum.lof (R.obj.obj V) _ _ φ))) x = (a.app V) x
    exact (DirectSum.toModule.unique _ (a.app V).hom x).symm
  right_inv a := by
    ext X x
    change (DirectSum.toModule (R.obj.obj (Opposite.op X.unop.left)) _
      (G.val.obj (Opposite.op X.unop.left))
      (fun φ : X.unop.left ⟶ U ↦ (a.val.app (Opposite.op (Over.mk φ))).hom))
        (DirectSum.lof _ _ _ X.unop.hom x) = (a.val.app X) x
    erw [DirectSum.toModule_lof]
    rfl

set_option backward.isDefEq.respectTransparency false in
private noncomputable def extensionSheafAdjunction
    {C : Type u} [SmallCategory C] {J : GrothendieckTopology C}
    (R : Sheaf J RingCat.{u}) (U : C) :
    (extensionByZeroPresheaf.{u} R U ⋙
      PresheafOfModules.sheafification.{u} (𝟙 R.obj)) ⊣ overFunctor.{u} R U := by
  refine Adjunction.mkOfHomEquiv ?_
  refine
    { homEquiv := fun F G ↦
        (PresheafOfModules.sheafificationHomEquiv (𝟙 R.obj)).trans
          (extensionPresheafHomEquiv R U F G)
      homEquiv_naturality_left_symm := ?_
      homEquiv_naturality_right := ?_ }
  · intro H F G a b
    change (PresheafOfModules.sheafificationHomEquiv (𝟙 R.obj)).symm
        ((extensionPresheafHomEquiv R U H G).symm (a ≫ b)) = _
    classical
    have hleft : (extensionPresheafHomEquiv R U H G).symm (a ≫ b) =
        (extensionByZeroPresheaf R U).map a ≫
          (extensionPresheafHomEquiv R U F G).symm b := by
      ext V x
      induction x using DirectSum.induction_on with
      | zero => simp
      | of φ x =>
        change (DirectSum.toModule (R.obj.obj V) _ (G.val.obj V)
          (fun ψ : V.unop ⟶ U ↦ ((a ≫ b).val.app
            (Opposite.op (Over.mk ψ))).hom)) (DirectSum.of _ φ x) =
          (DirectSum.toModule (R.obj.obj V) _ (G.val.obj V)
            (fun ψ : V.unop ⟶ U ↦ (b.val.app
              (Opposite.op (Over.mk ψ))).hom))
            (DirectSum.lmap (R := R.obj.obj V)
              (fun ψ : V.unop ⟶ U ↦ (a.val.app
                (Opposite.op (Over.mk ψ))).hom) (DirectSum.of _ φ x))
        erw [DirectSum.lmap_of, DirectSum.toModule_lof, DirectSum.toModule_lof]
        rfl
      | add x y hx hy => simpa only [map_add] using congrArg₂ (· + ·) hx hy
    rw [hleft]
    have h := (PresheafOfModules.sheafificationAdjunction (𝟙 R.obj)).homEquiv_naturality_left_symm
      ((extensionByZeroPresheaf R U).map a)
      ((extensionPresheafHomEquiv R U F G).symm b)
    have heq (P : _root_.PresheafOfModules.{u} R.obj) (G : SheafOfModules.{u} R) :
        (PresheafOfModules.sheafificationAdjunction (𝟙 R.obj)).homEquiv P G =
          PresheafOfModules.sheafificationHomEquiv (𝟙 R.obj) := by
      apply Equiv.ext
      intro f
      exact PresheafOfModules.sheafificationAdjunction_homEquiv_apply _ f
    rw [heq, heq] at h
    exact h
  · intro F G H a b
    change extensionPresheafHomEquiv R U F H
        (PresheafOfModules.sheafificationHomEquiv (𝟙 R.obj) (a ≫ b)) = _
    have h := (PresheafOfModules.sheafificationAdjunction (𝟙 R.obj)).homEquiv_naturality_right
      a b
    change PresheafOfModules.sheafificationHomEquiv (𝟙 R.obj) (a ≫ b) =
      PresheafOfModules.sheafificationHomEquiv (𝟙 R.obj) a ≫ b.val at h
    erw [h]
    ext X x
    rfl

/-- The canonical adjunction has the stated formula on each direct-sum injection. -/
theorem module_extensionByZero_hom_formula (X : Scheme.{u}) (U : X.Opens) :
    let R := X.ringCatSheaf
    let P := SheafOfModules.extensionByZeroPresheaf.{u} R U
    let L := P ⋙ PresheafOfModules.sheafification (𝟙 R.obj)
    ∃ adj : L ⊣ SheafOfModules.overFunctor R U,
        (∀ (F : SheafOfModules.{u} (R.over U)) (G : X.Modules)
          (ψ : L.obj F ⟶ G) (V : X.Opens) (h : V ⟶ U)
          (s : F.val.obj (op (Over.mk h))),
          ((adj.homEquiv F G ψ).val.app (op (Over.mk h))) s =
            (PresheafOfModules.sheafificationHomEquiv (𝟙 R.obj) ψ).app (op V)
              (DirectSum.of (fun φ : V ⟶ U => F.val.obj (op (Over.mk φ))) h s)) := by
  refine ⟨extensionSheafAdjunction X.ringCatSheaf U, ?_⟩
  intro F G ψ V h s
  simp only [extensionSheafAdjunction, Adjunction.mkOfHomEquiv_homEquiv,
    Equiv.trans_apply, extensionPresheafHomEquiv, Equiv.coe_fn_mk,
    extensionPresheafToHom]
  erw [ModuleCat.ofHom_apply, LinearMap.comp_apply, DirectSum.lof_eq_of]
  congr 1
  congr
  exact Subsingleton.elim _ _

end AlgebraicGeometry.Scheme.Modules
