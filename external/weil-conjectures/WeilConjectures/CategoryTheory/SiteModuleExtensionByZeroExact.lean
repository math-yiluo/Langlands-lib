/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.Abelian
public import WeilConjectures.CategoryTheory.ExtensionByZeroPresheaf
public import WeilConjectures.Mathlib.Algebra.Category.ModuleCat.Presheaf.Sheafification
import Mathlib.Algebra.Category.ModuleCat.Presheaf.EpiMono
import Mathlib.CategoryTheory.Adjunction.Additive

/-! # Exact module extension by zero with an independent ring universe

Source: Stacks Project, Modules on Sites, Tags 03DI and 03DJ.
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe c v r
open CategoryTheory CategoryTheory.Limits Opposite
namespace SheafOfModules

variable {C : Type c} [Category.{v} C] {J : GrothendieckTopology C}
  [HasSheafify J AddCommGrpCat.{max c v r}]
  [J.WEqualsLocallyBijective AddCommGrpCat.{max c v r}]
  (R : Sheaf J RingCat.{r}) (U : C)

/-- Sheafify the direct sum of sections over all maps to the slice object.
Source: Stacks Project, Tag 03DI.
(auxiliary; not a blueprint node).
-/
def siteModuleExtensionByZero :
    SheafOfModules.{max c v r} (R.over U) ⥤ SheafOfModules.{max c v r} R :=
  extensionByZeroPresheaf.{max c v r} R U ⋙
    PresheafOfModules.sheafification (𝟙 R.obj)

open Classical in
private theorem extensionRestrict_of
    {C : Type c} [Category.{v} C] {J : GrothendieckTopology C}
    (R : Sheaf J RingCat.{r}) (U : C)
    (F : SheafOfModules.{max c v r} (R.over U)) {V W : Cᵒᵖ} (a : V ⟶ W)
    (φ : V.unop ⟶ U) (ψ : W.unop ⟶ U) (h : a.unop ≫ φ = ψ)
    (x : F.val.obj (Opposite.op (Over.mk φ))) :
    extensionByZeroPresheafRestrictAdd R U F a
        (DirectSum.of (fun ψ : V.unop ⟶ U ↦ F.val.obj (Opposite.op (Over.mk ψ))) φ x) =
      DirectSum.of (fun χ : W.unop ⟶ U ↦ F.val.obj (Opposite.op (Over.mk χ))) ψ
        (F.val.map (Opposite.op (Over.homMk a.unop h : Over.mk ψ ⟶ Over.mk φ)) x) := by
  subst ψ
  change (DirectSum.toAddMonoid _)
    (DirectSum.of (fun ψ : V.unop ⟶ U ↦ F.val.obj (Opposite.op (Over.mk ψ))) φ x) = _
  rw [DirectSum.toAddMonoid_of]
  rfl

set_option backward.isDefEq.respectTransparency false in
set_option backward.defeqAttrib.useBackward true in
open Classical in
private noncomputable def extensionPresheafToHom
    {C : Type c} [Category.{v} C] {J : GrothendieckTopology C}
    (R : Sheaf J RingCat.{r}) (U : C)
    (F : SheafOfModules.{max c v r} (R.over U)) (G : SheafOfModules.{max c v r} R)
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
    have hr := extensionRestrict_of.{c, v, r} R U F ((Over.forget U).op.map f)
      X.unop.hom Y.unop.hom (Over.w f.unop) x
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
    {C : Type c} [Category.{v} C] {J : GrothendieckTopology C}
    (R : Sheaf J RingCat.{r}) (U : C)
    (F : SheafOfModules.{max c v r} (R.over U)) (G : SheafOfModules.{max c v r} R)
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
      erw [extensionRestrict_of.{c, v, r} R U F f φ (f.unop ≫ φ) rfl]
      erw [DirectSum.toModule_lof, DirectSum.toModule_lof]
      exact PresheafOfModules.naturality_apply a.val
        (Opposite.op (Over.homMk f.unop : Over.mk (f.unop ≫ φ) ⟶ Over.mk φ)) x
    | add x y hx hy => simpa only [map_add] using congrArg₂ (· + ·) hx hy

set_option backward.isDefEq.respectTransparency false in
open Classical in
private noncomputable def extensionPresheafHomEquiv
    {C : Type c} [Category.{v} C] {J : GrothendieckTopology C}
    (R : Sheaf J RingCat.{r}) (U : C)
    (F : SheafOfModules.{max c v r} (R.over U)) (G : SheafOfModules.{max c v r} R) :
    (extensionByZeroPresheafObj R U F ⟶ G.val) ≃
      (F ⟶ (overFunctor R U).obj G) where
  toFun := extensionPresheafToHom.{c, v, r} R U F G
  invFun := extensionHomToPresheaf.{c, v, r} R U F G
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
private theorem extensionPresheafHomEquiv_naturality_right
    {C : Type c} [Category.{v} C] {J : GrothendieckTopology C}
    (R : Sheaf J RingCat.{r}) (U : C)
    (F : SheafOfModules.{max c v r} (R.over U)) (G H : SheafOfModules.{max c v r} R)
    (a : extensionByZeroPresheafObj R U F ⟶ G.val) (b : G ⟶ H) :
    extensionPresheafHomEquiv.{c, v, r} R U F H (a ≫ b.val) =
      extensionPresheafHomEquiv.{c, v, r} R U F G a ≫ (overFunctor R U).map b := by
  ext X x
  rfl

set_option backward.isDefEq.respectTransparency false in
open Classical in
private theorem extensionPresheafHomEquiv_naturality_left_symm
    {C : Type c} [Category.{v} C] {J : GrothendieckTopology C}
    (R : Sheaf J RingCat.{r}) (U : C)
    (F H : SheafOfModules.{max c v r} (R.over U)) (G : SheafOfModules.{max c v r} R)
    (a : H ⟶ F) (b : F ⟶ (overFunctor R U).obj G) :
    (extensionPresheafHomEquiv.{c, v, r} R U H G).symm (a ≫ b) =
      (extensionByZeroPresheaf R U).map a ≫
        (extensionPresheafHomEquiv.{c, v, r} R U F G).symm b := by
  ext V x
  induction x using DirectSum.induction_on with
  | zero => simp
  | of φ x =>
    change (DirectSum.toModule (R.obj.obj V) _ (G.val.obj V)
      (fun ψ : V.unop ⟶ U ↦ ((a ≫ b).val.app (Opposite.op (Over.mk ψ))).hom))
        (DirectSum.of _ φ x) =
      (DirectSum.toModule (R.obj.obj V) _ (G.val.obj V)
        (fun ψ : V.unop ⟶ U ↦ (b.val.app (Opposite.op (Over.mk ψ))).hom))
          (DirectSum.lmap (R := R.obj.obj V)
            (fun ψ : V.unop ⟶ U ↦ (a.val.app (Opposite.op (Over.mk ψ))).hom)
              (DirectSum.of _ φ x))
    erw [DirectSum.lmap_of, DirectSum.toModule_lof, DirectSum.toModule_lof]
    rfl
  | add x y hx hy => simpa only [map_add] using congrArg₂ (· + ·) hx hy

set_option backward.isDefEq.respectTransparency false in
private noncomputable def extensionSheafAdjunction
    {C : Type c} [Category.{v} C] {J : GrothendieckTopology C}
    [HasSheafify J AddCommGrpCat.{max c v r}]
    [J.WEqualsLocallyBijective AddCommGrpCat.{max c v r}]
    (R : Sheaf J RingCat.{r}) (U : C) :
    (extensionByZeroPresheaf.{max c v r} R U ⋙
      PresheafOfModules.sheafification.{max c v r} (𝟙 R.obj)) ⊣ overFunctor.{max c v r} R U := by
  refine Adjunction.mkOfHomEquiv ?_
  refine
    { homEquiv := fun F G ↦
        (PresheafOfModules.sheafificationHomEquiv (𝟙 R.obj)).trans
          (extensionPresheafHomEquiv.{c, v, r} R U F G)
      homEquiv_naturality_left_symm := ?_
      homEquiv_naturality_right := ?_ }
  · intro H F G a b
    change (PresheafOfModules.sheafificationHomEquiv (𝟙 R.obj)).symm
        ((extensionPresheafHomEquiv.{c, v, r} R U H G).symm (a ≫ b)) = _
    rw [extensionPresheafHomEquiv_naturality_left_symm.{c, v, r}]
    have h := (PresheafOfModules.sheafificationAdjunction (𝟙 R.obj)).homEquiv_naturality_left_symm
      ((extensionByZeroPresheaf R U).map a)
      ((extensionPresheafHomEquiv.{c, v, r} R U F G).symm b)
    have heq (P : PresheafOfModules.{max c v r} R.obj) (G : SheafOfModules.{max c v r} R) :
        (PresheafOfModules.sheafificationAdjunction (𝟙 R.obj)).homEquiv P G =
          PresheafOfModules.sheafificationHomEquiv (𝟙 R.obj) := by
      apply Equiv.ext
      intro f
      exact PresheafOfModules.sheafificationAdjunction_homEquiv_apply _ f
    rw [heq, heq] at h
    exact h
  · intro F G H a b
    change extensionPresheafHomEquiv.{c, v, r} R U F H
        (PresheafOfModules.sheafificationHomEquiv (𝟙 R.obj) (a ≫ b)) = _
    have h := (PresheafOfModules.sheafificationAdjunction (𝟙 R.obj)).homEquiv_naturality_right
      a b
    change PresheafOfModules.sheafificationHomEquiv (𝟙 R.obj) (a ≫ b) =
      PresheafOfModules.sheafificationHomEquiv (𝟙 R.obj) a ≫ b.val at h
    erw [h]
    exact extensionPresheafHomEquiv_naturality_right.{c, v, r} R U F G H _ b

/-- Extension by zero is exact and left adjoint to restriction, with no identification
of the ring universe and the site universes.
Source: Stacks Project, Modules on Sites, Tags 03DI and 03DJ.
(auxiliary; not a blueprint node).

Proof: A map from the direct-sum presheaf is uniquely a compatible map from every
summand. Evaluating the corresponding restriction map on a slice object, and inserting
its structure-map summand, gives inverse Hom correspondences. Sheafification extends
this correspondence to module sheaves, producing the adjunction. Restriction is additive
sectionwise, so its left adjoint is additive. It preserves finite colimits by adjunction.
Evaluation of a sheaf monomorphism is injective; the direct sum of these injections is
injective. Hence presheaf extension preserves monomorphisms. Left exact sheafification
preserves them as well. An additive right exact functor preserving monomorphisms is
exact, which gives finite-limit preservation. This argument works for any object U;
subterminality and a cover are not required, including empty sites and zero rings.
-/
theorem siteModuleExtensionByZero_exact
    [HasSheafify (J.over U) AddCommGrpCat.{max c v r}]
    [(J.over U).WEqualsLocallyBijective AddCommGrpCat.{max c v r}] :
    (siteModuleExtensionByZero R U).Additive ∧
    PreservesFiniteLimits (siteModuleExtensionByZero R U) ∧
    PreservesFiniteColimits (siteModuleExtensionByZero R U) ∧
    Nonempty (siteModuleExtensionByZero R U ⊣ overFunctor.{max c v r} R U) := by
  let L := siteModuleExtensionByZero R U
  let T := overFunctor.{max c v r} R U
  let adj : L ⊣ T := extensionSheafAdjunction.{c, v, r} R U
  have : PreservesColimitsOfSize.{0, 0} L := adj.leftAdjoint_preservesColimits
  have : T.Additive := by
    constructor
    intro X Y f g
    ext V x
    rfl
  have : L.Additive := adj.left_adjoint_additive
  have : (extensionByZeroPresheaf.{max c v r} R U).PreservesMonomorphisms := by
    constructor
    intro X Y f hf
    apply PresheafOfModules.mono_of_injective
    intro V
    change Function.Injective (DirectSum.lmap (R := R.obj.obj V)
      (fun φ : V.unop ⟶ U ↦ (f.val.app (op (Over.mk φ))).hom))
    apply (DirectSum.lmap_injective _).mpr
    intro φ
    apply (ModuleCat.mono_iff_injective _).mp
    exact inferInstanceAs (Mono ((evaluation.{max c v r} (R.over U) (op (Over.mk φ))).map f))
  have : L.PreservesMonomorphisms :=
    inferInstanceAs ((extensionByZeroPresheaf.{max c v r} R U ⋙
      PresheafOfModules.sheafification.{max c v r} (𝟙 R.obj)).PreservesMonomorphisms)
  have : L.PreservesHomology := L.preservesHomology_of_preservesMonos_and_cokernels
  have : PreservesFiniteLimits L := L.preservesFiniteLimits_of_preservesHomology
  exact ⟨inferInstance, inferInstance, inferInstance, ⟨adj⟩⟩

end SheafOfModules
