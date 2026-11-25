/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.AlgebraicGeometry.FundamentalGroup.Restriction

/-!
# Elementary paths between fibre functors

A *path* from a geometric point `y` to a geometric point `z` of a scheme `Y` is an isomorphism
`F_y ≅ F_z` of the fibre functors on finite étale `Y`-schemes. This file provides two elementary
sources of paths:

* reparametrising a geometric point `y : Spec Ω ⟶ Y` by an automorphism `a` of `Spec Ω` gives the
  path `F_{a ≫ y} ≅ F_y`, `x ↦ a⁻¹ ≫ x`
  (`AlgebraicGeometry.Scheme.FiniteEtale.fiberReparamIso`);
* a path `τ : F_y ≅ F_z` on `FÉt(X)` is carried by a morphism `f : X ⟶ Y` to a path
  `F_{y ≫ f} ≅ F_{z ≫ f}` on `FÉt(Y)`, through base change of finite étale schemes along `f`
  and the identification of `F_y ∘ f^*` with `F_{y ≫ f}`
  (`AlgebraicGeometry.Scheme.FiniteEtale.pullbackPathIso`).

These are the paths along which the stalks of lisse sheaves are transported in
`WeilConjectures.SixFunctors.ProEtale.Adic.LisseMonodromy`.
-/

@[expose] public section

universe u

open CategoryTheory Limits

namespace AlgebraicGeometry.Scheme.FiniteEtale

variable {X Y : Scheme.{u}} {Ω : Type u} [Field Ω] [IsSepClosed Ω]

/-- The path `F_{a ≫ y} ≅ F_y` attached to an automorphism `a` of `Spec Ω` and a geometric point
`y : Spec Ω ⟶ Y`: a point `x` of the fibre at `a ≫ y` goes to the point `a⁻¹ ≫ x` of the fibre
at `y`. -/
noncomputable def fiberReparamIso (a : Spec (.of Ω) ≅ Spec (.of Ω)) (y : Spec (.of Ω) ⟶ Y) :
    fiber (a.hom ≫ y) ≅ fiber y :=
  NatIso.ofComponents
    (fun P ↦ FintypeCat.equivEquivIso
      { toFun x := fiberMk y P (a.inv ≫ x.left) (by
          rw [Category.assoc, fiber_left_comp, a.inv_hom_id_assoc])
        invFun x := fiberMk (a.hom ≫ y) P (a.hom ≫ x.left) (by
          rw [Category.assoc, fiber_left_comp])
        left_inv x := fiber_ext _ (by simp)
        right_inv x := fiber_ext _ (by simp) })
    (by
      intro P Q φ
      ext x
      exact fiber_ext y (Category.assoc a.inv x.left φ.hom.left).symm)

/-- The reparametrisation path on points: precomposition with `a⁻¹`. -/
@[simp]
lemma fiberReparamIso_hom_app_left (a : Spec (.of Ω) ≅ Spec (.of Ω)) (y : Spec (.of Ω) ⟶ Y)
    (P : Y.FiniteEtale) (x : (fiber (a.hom ≫ y)).obj P) :
    ((fiberReparamIso a y).hom.app P x).left = a.inv ≫ x.left :=
  rfl

/-- The inverse reparametrisation path on points: precomposition with `a`. -/
@[simp]
lemma fiberReparamIso_inv_app_left (a : Spec (.of Ω) ≅ Spec (.of Ω)) (y : Spec (.of Ω) ⟶ Y)
    (P : Y.FiniteEtale) (x : (fiber y).obj P) :
    ((fiberReparamIso a y).inv.app P x).left = a.hom ≫ x.left :=
  rfl

/-- The path `F_{y ≫ f} ≅ F_{z ≫ f}` on `FÉt(Y)` induced by a path `τ : F_y ≅ F_z` on `FÉt(X)`
and a morphism `f : X ⟶ Y`: `F_{y ≫ f} ≅ F_y ∘ f^* ≅ F_z ∘ f^* ≅ F_{z ≫ f}`. -/
noncomputable def pullbackPathIso (f : X ⟶ Y) {y z : Spec (.of Ω) ⟶ X}
    (τ : fiber y ≅ fiber z) : fiber (y ≫ f) ≅ fiber (z ≫ f) :=
  (pullbackFiberIso f y).symm ≪≫ Functor.isoWhiskerLeft (pullback f) τ ≪≫ pullbackFiberIso f z

/-- The trivial path induces the trivial path. -/
lemma pullbackPathIso_refl (f : X ⟶ Y) (y : Spec (.of Ω) ⟶ X) :
    pullbackPathIso f (Iso.refl (fiber y)) = Iso.refl _ := by
  ext P x
  simp [pullbackPathIso]

/-- Inducing paths along `f` is compatible with composition of paths. -/
lemma pullbackPathIso_trans (f : X ⟶ Y) {y z w : Spec (.of Ω) ⟶ X} (τ : fiber y ≅ fiber z)
    (τ' : fiber z ≅ fiber w) :
    pullbackPathIso f (τ ≪≫ τ') = pullbackPathIso f τ ≪≫ pullbackPathIso f τ' := by
  ext P x
  simp [pullbackPathIso]

/-- The point of the base change `P ×_Y X` at `y` corresponding to a point `x` of `P` at `y ≫ f`
is the lift `(x, y)`. -/
@[simp]
lemma pullbackFiberIso_inv_app_left (f : X ⟶ Y) (y : Spec (.of Ω) ⟶ X) (P : Y.FiniteEtale)
    (x : (fiber (y ≫ f)).obj P) :
    ((pullbackFiberIso f y).inv.app P x).left =
      Limits.pullback.lift x.left y (fiber_left_comp _ x) :=
  rfl

/-- Elementwise description of `pullbackPathIso`: the image of `x` is the first projection of
the image under `τ` of the point `(x, y)` of the base change. -/
lemma pullbackPathIso_hom_app_left (f : X ⟶ Y) {y z : Spec (.of Ω) ⟶ X}
    (τ : fiber y ≅ fiber z) (P : Y.FiniteEtale) (x : (fiber (y ≫ f)).obj P) :
    ((pullbackPathIso f τ).hom.app P x).left =
      (τ.hom.app ((pullback f).obj P) ((pullbackFiberIso f y).inv.app P x)).left ≫
        Limits.pullback.fst P.obj.hom f :=
  rfl

/-- Transport along an equality of fibre functors coming from an equality of geometric points
does not change the underlying morphism of a point. -/
lemma eqToIso_fiber_hom_app_left {y z : Spec (.of Ω) ⟶ Y} (hyz : y = z) (h : fiber y = fiber z)
    (P : Y.FiniteEtale) (x : (fiber y).obj P) : ((eqToIso h).hom.app P x).left = x.left := by
  subst hyz
  rfl

/-- Inducing paths along `f` is compatible with inverses of paths. -/
lemma pullbackPathIso_symm (f : X ⟶ Y) {y z : Spec (.of Ω) ⟶ X} (τ : fiber y ≅ fiber z) :
    pullbackPathIso f τ.symm = (pullbackPathIso f τ).symm := by
  ext P x
  simp [pullbackPathIso]

/-- The path induced by an equality of geometric points is the equality of the images. -/
lemma pullbackPathIso_eqToIso (f : X ⟶ Y) {y z : Spec (.of Ω) ⟶ X} (h : y = z) :
    pullbackPathIso f (eqToIso (congrArg fiber h)) = eqToIso (by rw [h]) := by
  subst h
  simp [pullbackPathIso_refl]

/-- Transporting a path along equal morphisms. -/
lemma pullbackPathIso_congr {f f' : X ⟶ Y} (hf : f = f') {y z : Spec (.of Ω) ⟶ X}
    (τ : fiber y ≅ fiber z) :
    pullbackPathIso f τ = eqToIso (by rw [hf]) ≪≫ pullbackPathIso f' τ ≪≫ eqToIso (by rw [hf]) := by
  subst hf
  simp

/-- The comparison morphism `(P ×_Z Y) ×_Y X ⟶ P ×_Z X` of finite étale `X`-schemes. -/
noncomputable def pullbackCompHom {Z : Scheme.{u}} (f : X ⟶ Y) (g : Y ⟶ Z) (P : Z.FiniteEtale) :
    (pullback f).obj ((pullback g).obj P) ⟶ (pullback (f ≫ g)).obj P :=
  ObjectProperty.homMk (MorphismProperty.Over.homMk
    (Limits.pullback.lift (Limits.pullback.fst _ _ ≫ Limits.pullback.fst _ _)
      (Limits.pullback.snd _ _) (by
        change (Limits.pullback.fst _ _ ≫ Limits.pullback.fst P.obj.hom g) ≫ P.obj.hom =
          Limits.pullback.snd (Limits.pullback.snd P.obj.hom g) f ≫ f ≫ g
        rw [Category.assoc, Limits.pullback.condition, ← Category.assoc,
          Limits.pullback.condition, Category.assoc]))
    (Limits.pullback.lift_snd _ _ _))

/-- The underlying morphism of `pullbackCompHom` is the lift `(fst ≫ fst, snd)`. -/
@[simp]
lemma pullbackCompHom_hom_left {Z : Scheme.{u}} (f : X ⟶ Y) (g : Y ⟶ Z) (P : Z.FiniteEtale) :
    (pullbackCompHom f g P).hom.left =
      Limits.pullback.lift (Limits.pullback.fst _ _ ≫ Limits.pullback.fst _ _)
        (Limits.pullback.snd _ _) (by
          change (Limits.pullback.fst _ _ ≫ Limits.pullback.fst P.obj.hom g) ≫ P.obj.hom =
            Limits.pullback.snd (Limits.pullback.snd P.obj.hom g) f ≫ f ≫ g
          rw [Category.assoc, Limits.pullback.condition, ← Category.assoc,
            Limits.pullback.condition, Category.assoc]) :=
  rfl

/-- The path induced along a composite is the iterated induced path. -/
lemma pullbackPathIso_comp {Z : Scheme.{u}} (f : X ⟶ Y) (g : Y ⟶ Z) {y z : Spec (.of Ω) ⟶ X}
    (τ : fiber y ≅ fiber z) :
    pullbackPathIso (f ≫ g) τ =
      eqToIso (by rw [Category.assoc]) ≪≫ pullbackPathIso g (pullbackPathIso f τ) ≪≫
        eqToIso (by rw [Category.assoc]) := by
  ext P x
  apply fiber_ext
  rw [Iso.trans_hom, Iso.trans_hom, NatTrans.comp_app, NatTrans.comp_app, FintypeCat.comp_apply,
    FintypeCat.comp_apply]
  rw [eqToIso_fiber_hom_app_left (Category.assoc z f g), pullbackPathIso_hom_app_left,
    pullbackPathIso_hom_app_left, pullbackPathIso_hom_app_left]
  have hx : ((eqToIso (congrArg fiber (Category.assoc y f g)).symm).hom.app P x).left = x.left :=
    eqToIso_fiber_hom_app_left (Category.assoc y f g).symm _ P x
  have hw : (fiber y).map (pullbackCompHom f g P) ((pullbackFiberIso f y).inv.app _
      ((pullbackFiberIso g (y ≫ f)).inv.app P
        ((eqToIso (congrArg fiber (Category.assoc y f g)).symm).hom.app P x))) =
      (pullbackFiberIso (f ≫ g) y).inv.app P x := by
    apply fiber_ext
    rw [fiber_map_left, pullbackCompHom_hom_left, pullbackFiberIso_inv_app_left f y,
      pullbackFiberIso_inv_app_left (f ≫ g) y]
    apply Limits.pullback.hom_ext
    · rw [Category.assoc, Limits.pullback.lift_fst, Limits.pullback.lift_fst_assoc,
        Limits.pullback.lift_fst, pullbackFiberIso_inv_app_left, Limits.pullback.lift_fst, hx]
    · rw [Category.assoc, Limits.pullback.lift_snd, Limits.pullback.lift_snd,
        Limits.pullback.lift_snd]
  rw [← hw, ← ConcreteCategory.comp_apply, τ.hom.naturality, ConcreteCategory.comp_apply,
    fiber_map_left, pullbackCompHom_hom_left]
  simp only [Category.assoc, Limits.pullback.lift_fst]

/-- The path induced by a reparametrisation path is the reparametrisation path of the image. -/
lemma pullbackPathIso_fiberReparamIso (f : X ⟶ Y) (a : Spec (.of Ω) ≅ Spec (.of Ω))
    (y : Spec (.of Ω) ⟶ X) :
    pullbackPathIso f (fiberReparamIso a y) =
      eqToIso (by rw [Category.assoc]) ≪≫ fiberReparamIso a (y ≫ f) := by
  ext P x
  apply fiber_ext
  rw [Iso.trans_hom, NatTrans.comp_app, FintypeCat.comp_apply]
  rw [fiberReparamIso_hom_app_left, eqToIso_fiber_hom_app_left (Category.assoc a.hom y f),
    pullbackPathIso_hom_app_left, fiberReparamIso_hom_app_left, Category.assoc,
    pullbackFiberIso_inv_app_left, Limits.pullback.lift_fst]

/-- A path `τ : F_y ≅ F_z` carries the point of a finite étale `P` on a section `σ` at `y` to the
point on the same section at `z`: naturality with respect to the morphism `Y ⟶ P` of finite
étale `Y`-schemes given by `σ`, the fibres of `Y` itself being points. -/
lemma path_section {y z : Spec (.of Ω) ⟶ Y} (τ : fiber y ≅ fiber z) (P : Y.FiniteEtale)
    (σ : Y ⟶ P.obj.left) (hσ : σ ≫ P.obj.hom = 𝟙 Y) (x : (fiber y).obj P)
    (hx : x.left = y ≫ σ) :
    (τ.hom.app P x).left = z ≫ σ := by
  let T : Y.FiniteEtale :=
    ⟨MorphismProperty.Over.mk ⊤ (𝟙 Y) inferInstance, inferInstanceAs (IsFinite (𝟙 Y))⟩
  let S : T ⟶ P := ObjectProperty.homMk (MorphismProperty.Over.homMk σ hσ)
  let x₁ : (fiber y).obj T := fiberMk y T y (Category.comp_id y)
  have hx₁ : (fiber y).map S x₁ = x := fiber_ext y <| by
    rw [fiber_map_left, hx]
    rfl
  have key : τ.hom.app P x = (fiber z).map S (τ.hom.app T x₁) := by
    rw [← hx₁]
    exact ConcreteCategory.congr_hom (τ.hom.naturality S) x₁
  have h₀ : (τ.hom.app T x₁).left = z := by
    rw [← Category.comp_id (τ.hom.app T x₁).left]
    exact fiber_left_comp z (τ.hom.app T x₁)
  rw [key, fiber_map_left, h₀]
  rfl

end AlgebraicGeometry.Scheme.FiniteEtale
