/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import Mathlib.Algebra.Category.ModuleCat.Sheaf.PushforwardContinuous
import Mathlib.Algebra.Category.Grp.FilteredColimits
import Mathlib.Algebra.Category.ModuleCat.Presheaf.EpiMono
import Mathlib.Algebra.Category.ModuleCat.Sheaf.Abelian
import Mathlib.Algebra.Homology.ShortComplex.ExactFunctor
import Mathlib.CategoryTheory.Adjunction.Additive
import WeilConjectures.CategoryTheory.ExtensionByZeroPresheaf

/-!
# Exact extension for localized restriction of module sheaves

Source: Stacks Project, Modules on Sites, Lemmas 03DI and 03DJ.
(blueprint: new-localized-restriction-extension-exists)

The private Hom-equivalence helpers generalize the proved helpers of
`WeilConjectures.CategoryTheory.LocalizedModuleAdjunctionExact` to independent object and
morphism universes, arbitrary Grothendieck topologies, and noncommutative rings.
The explicit presheaf functor is reused from `ExtensionByZeroPresheaf`.
-/

@[expose] public section

universe u v

open CategoryTheory CategoryTheory.Limits

namespace CategoryTheory

open SheafOfModules Classical in
private theorem extensionRestrict_of
    {C : Type u} [Category.{v} C] {J : GrothendieckTopology C}
    (R : Sheaf J RingCat.{max u v}) (U : C)
    (F : SheafOfModules.{max u v} (R.over U)) {V W : Cᵒᵖ} (a : V ⟶ W)
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
open SheafOfModules Classical in
private noncomputable def extensionPresheafToHom
    {C : Type u} [Category.{v} C] {J : GrothendieckTopology C}
    (R : Sheaf J RingCat.{max u v}) (U : C)
    (F : SheafOfModules.{max u v} (R.over U)) (G : SheafOfModules.{max u v} R)
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
    have hr := extensionRestrict_of R U F ((Over.forget U).op.map f)
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
open SheafOfModules Classical in
private noncomputable def extensionHomToPresheaf
    {C : Type u} [Category.{v} C] {J : GrothendieckTopology C}
    (R : Sheaf J RingCat.{max u v}) (U : C)
    (F : SheafOfModules.{max u v} (R.over U)) (G : SheafOfModules.{max u v} R)
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
      erw [extensionRestrict_of R U F f φ (f.unop ≫ φ) rfl]
      erw [DirectSum.toModule_lof, DirectSum.toModule_lof]
      exact PresheafOfModules.naturality_apply a.val
        (Opposite.op (Over.homMk f.unop : Over.mk (f.unop ≫ φ) ⟶ Over.mk φ)) x
    | add x y hx hy => simpa only [map_add] using congrArg₂ (· + ·) hx hy

set_option backward.isDefEq.respectTransparency false in
open SheafOfModules Classical in
private noncomputable def extensionPresheafHomEquiv
    {C : Type u} [Category.{v} C] {J : GrothendieckTopology C}
    (R : Sheaf J RingCat.{max u v}) (U : C)
    (F : SheafOfModules.{max u v} (R.over U)) (G : SheafOfModules.{max u v} R) :
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
open SheafOfModules in
private theorem extensionPresheafHomEquiv_naturality_right
    {C : Type u} [Category.{v} C] {J : GrothendieckTopology C}
    (R : Sheaf J RingCat.{max u v}) (U : C)
    (F : SheafOfModules.{max u v} (R.over U)) (G H : SheafOfModules.{max u v} R)
    (a : extensionByZeroPresheafObj R U F ⟶ G.val) (b : G ⟶ H) :
    extensionPresheafHomEquiv R U F H (a ≫ b.val) =
      extensionPresheafHomEquiv R U F G a ≫ (overFunctor R U).map b := by
  ext X x
  rfl

set_option backward.isDefEq.respectTransparency false in
open SheafOfModules Classical in
private theorem extensionPresheafHomEquiv_naturality_left_symm
    {C : Type u} [Category.{v} C] {J : GrothendieckTopology C}
    (R : Sheaf J RingCat.{max u v}) (U : C)
    (F H : SheafOfModules.{max u v} (R.over U)) (G : SheafOfModules.{max u v} R)
    (a : H ⟶ F) (b : F ⟶ (overFunctor R U).obj G) :
    (extensionPresheafHomEquiv R U H G).symm (a ≫ b) =
      (extensionByZeroPresheaf R U).map a ≫
        (extensionPresheafHomEquiv R U F G).symm b := by
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
open SheafOfModules in
private noncomputable def extensionSheafAdjunction
    {C : Type u} [Category.{v} C] {J : GrothendieckTopology C}
    (R : Sheaf J RingCat.{max u v}) (U : C) :
    (extensionByZeroPresheaf.{max u v} R U ⋙
      PresheafOfModules.sheafification.{max u v} (𝟙 R.obj)) ⊣ overFunctor.{max u v} R U := by
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
    rw [extensionPresheafHomEquiv_naturality_left_symm]
    have h := (PresheafOfModules.sheafificationAdjunction (𝟙 R.obj)).homEquiv_naturality_left_symm
      ((extensionByZeroPresheaf R U).map a)
      ((extensionPresheafHomEquiv R U F G).symm b)
    have heq (P : PresheafOfModules.{max u v} R.obj) (G : SheafOfModules.{max u v} R) :
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
    exact extensionPresheafHomEquiv_naturality_right R U F G H _ b


/-- For a sheaf of rings on a Grothendieck site and an object `U`, localized
restriction admits a left adjoint preserving finite limits and finite colimits.

Proof: for a localized module sheaf `N`, define a presheaf `P(N)` with sections
at `V` the direct sum of `N(V, f)` over arrows `f : V ⟶ U`. The ring `R(V)` acts
on each summand. A restriction along `a : W ⟶ V` sends the `f` summand by the
restriction of `N` into the `a ≫ f` summand. The identities and composition laws
follow on direct-sum generators from those of `N`. A morphism of localized
sheaves acts on each summand; these maps define an additive functor `P`.
Let `G(N)` be module sheafification of `P(N)`.

A morphism `N ⟶ M.over U` gives a presheaf morphism `P(N) ⟶ M.val` by summing
its components. Conversely, compose such a presheaf morphism with each summand
inclusion to recover the components of a morphism `N ⟶ M.over U`. Naturality
along arrows in `C/U` follows from the restriction formula. The constructions
are inverse on generators and natural in both sheaves. The universal property
of module sheafification therefore gives `G ⊣ restriction`.

A monomorphism of module sheaves is injective on sections: its kernel is the
sectionwise kernel. Direct sums of injections are injective, so `P` sends a
monomorphism to a sectionwise injection. Exact module sheafification sends
this to a monomorphism. Sheafification is additive, so `G` is additive. As a
left adjoint it preserves colimits, hence is right exact. An additive right
exact functor between abelian categories that preserves monomorphisms is exact:
apply it to the two short exact sequences factoring an exact sequence through
its image. Thus `G` preserves kernels and finite biproducts, hence finite
limits; the adjunction already gives preservation of finite colimits.
This argument also covers empty indexing sets, whose direct sums are zero.
No assumption of commutativity of the rings or of pullbacks in `C` is needed.

Source: Stacks Project, Tags 03DI and 03DJ (Modules on Sites, Lemmas 18.19.2
and 18.19.3); Tag 08FI uses this exact left adjoint.
(blueprint: new-localized-restriction-extension-exists)
-/
theorem localized_restriction_extension_exists
    {C : Type u} [Category.{v} C] {J : GrothendieckTopology C}
    (R : Sheaf J RingCat.{max u v}) (U : C)
    (hzero : (SheafOfModules.overFunctor.{max u v} R U).PreservesZeroMorphisms) :
    ∃ (G : SheafOfModules.{max u v} (R.over U) ⥤ SheafOfModules.{max u v} R),
      PreservesFiniteLimits G ∧ PreservesFiniteColimits G ∧
      Nonempty (G ⊣ SheafOfModules.overFunctor.{max u v} R U) := by
  let G := SheafOfModules.extensionByZeroPresheaf.{max u v} R U ⋙
    PresheafOfModules.sheafification.{max u v} (𝟙 R.obj)
  let adj : G ⊣ SheafOfModules.overFunctor.{max u v} R U := extensionSheafAdjunction R U
  have : (SheafOfModules.overFunctor.{max u v} R U).PreservesZeroMorphisms := hzero
  have : (SheafOfModules.overFunctor.{max u v} R U).Additive := by
    constructor
    intro X Y f g
    ext V x
    rfl
  have : G.Additive := adj.left_adjoint_additive
  have : PreservesColimitsOfSize.{0, 0} G := adj.leftAdjoint_preservesColimits
  have : (SheafOfModules.extensionByZeroPresheaf.{max u v} R U).PreservesMonomorphisms := by
    constructor
    intro X Y f hf
    classical
    apply PresheafOfModules.mono_of_injective
    intro V
    change Function.Injective
      (DirectSum.lmap (R := R.obj.obj V)
        (fun φ : V.unop ⟶ U ↦ (f.val.app (Opposite.op (Over.mk φ))).hom))
    apply (DirectSum.lmap_injective _).mpr
    intro φ
    apply (ModuleCat.mono_iff_injective _).mp
    exact (SheafOfModules.evaluation (R.over U) (Opposite.op (Over.mk φ))).map_mono f
  have : G.PreservesMonomorphisms := inferInstance
  have : G.PreservesHomology :=
    Functor.preservesHomology_of_preservesMonos_and_cokernels G
  exact ⟨G, G.preservesFiniteLimits_of_preservesHomology, inferInstance, ⟨adj⟩⟩

end CategoryTheory
