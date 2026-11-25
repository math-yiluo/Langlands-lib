/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import Mathlib.Algebra.Category.ModuleCat.Colimits
public import Mathlib.CategoryTheory.Generator.Sheaf
public import Mathlib.CategoryTheory.Sites.Point.Skyscraper
public import Mathlib.LinearAlgebra.Finsupp.LinearCombination

/-!
# The fibre of a free sheaf at a point

Let `Φ` be a point of a site `(C, J)`, `X : C` and `R` a commutative ring. The free presheaf
`R[X] = Presheaf.freeYoneda X R`, sending `U` to the free `R`-module on `U ⟶ X`, has fibre at
`Φ` the free `R`-module on the fibre `Φ.fiber.obj X`; the same holds for the free sheaf
`Sheaf.freeYoneda J X R`, whose fibre is that of its presheaf. The basis element attached to
`x : Φ.fiber.obj X` is the germ at `(X, x)` of the generator, the image of `𝟙 X`.

The universes are those of the small étale site of a scheme: a category with morphisms in
`Type u`, a point with fibres in `Type u` and modules in `Type (u + 1)`.

## Main definitions

- `CategoryTheory.GrothendieckTopology.Point.presheafFiberFreeYonedaIso`
- `CategoryTheory.GrothendieckTopology.Point.sheafFiberFreeYonedaEquiv`
-/

@[expose] public section

universe u u'

namespace CategoryTheory.GrothendieckTopology.Point

open Limits Opposite

variable {C : Type u'} [Category.{u} C] {J : GrothendieckTopology C} (Φ : Point.{u} J)
  (R : Type (u + 1)) [CommRing R]

/-- The generator of the free presheaf `R[X]` over `X`: the basis element attached to `𝟙 X`. -/
noncomputable def freeYonedaGen (X : C) :
    (Presheaf.freeYoneda X (ModuleCat.of R R)).obj (op X) :=
  (Sigma.ι (fun _ : (yoneda.obj X).obj (op X) ↦ ModuleCat.of R R) (𝟙 X)).hom (1 : R)

/-- The basis element `f : U ⟶ X` of `R[X](U)` is the restriction of the generator along `f`. -/
lemma freeYoneda_map_freeYonedaGen (X U : C) (f : U ⟶ X) :
    (Presheaf.freeYoneda X (ModuleCat.of R R)).map f.op (freeYonedaGen R X) =
      (Sigma.ι (fun _ : (yoneda.obj X).obj (op U) ↦ ModuleCat.of R R) f).hom 1 := by
  have h := ConcreteCategory.congr_hom (Sigma.ι_comp_map'
    (g := fun _ : (yoneda.obj X).obj (op X) ↦ ModuleCat.of R R)
    (f := fun _ : (yoneda.obj X).obj (op U) ↦ ModuleCat.of R R)
    ((yoneda.obj X).map f.op) (fun _ ↦ 𝟙 _) (𝟙 X)) (1 : R)
  rw [freeYonedaGen, Presheaf.freeYoneda_map]
  simp only [ConcreteCategory.comp_apply, ConcreteCategory.id_apply] at h
  refine h.trans ?_
  simp

set_option backward.isDefEq.respectTransparency false in
/-- Compatibility of the maps defining `presheafFiberFreeYonedaDesc`. -/
lemma presheafFiberFreeYonedaDesc_w (X : C) ⦃U U' : C⦄ (g : U ⟶ U') (u : Φ.fiber.obj U) :
    (Presheaf.freeYoneda X (ModuleCat.of R R)).map g.op ≫
        (Sigma.desc (f := fun _ : (yoneda.obj X).obj (op U) ↦ ModuleCat.of R R) fun f ↦
          ModuleCat.ofHom (Finsupp.lsingle (R := R) (Φ.fiber.map f u))) =
      Sigma.desc (f := fun _ : (yoneda.obj X).obj (op U') ↦ ModuleCat.of R R) fun f ↦
        ModuleCat.ofHom (Finsupp.lsingle (R := R) (Φ.fiber.map f (Φ.fiber.map g u))) := by
  refine Sigma.hom_ext _ _ fun f ↦ ?_
  simp only [Presheaf.freeYoneda_map]
  rw [Sigma.ι_comp_map'_assoc, Category.id_comp, Sigma.ι_comp_desc, Sigma.ι_comp_desc]
  simp

/-- The map from the fibre of the free presheaf `R[X]` to the free module on `Φ.fiber.obj X`,
sending the germ at `(U, u)` of the basis element `f : U ⟶ X` to `Φ.fiber.map f u`. -/
noncomputable def presheafFiberFreeYonedaDesc (X : C) :
    Φ.presheafFiber.obj (Presheaf.freeYoneda X (ModuleCat.of R R)) ⟶
      ModuleCat.of R (Φ.fiber.obj X →₀ R) :=
  Φ.presheafFiberDesc (P := Presheaf.freeYoneda X (ModuleCat.of R R))
    (fun _ u ↦ Sigma.desc fun f ↦ ModuleCat.ofHom (Finsupp.lsingle (Φ.fiber.map f u)))
    (Φ.presheafFiberFreeYonedaDesc_w R X)


set_option backward.isDefEq.respectTransparency false in
/-- `presheafFiberFreeYonedaDesc` on the germ of a basis element. -/
lemma ι_toPresheafFiber_presheafFiberFreeYonedaDesc (X U : C) (u : Φ.fiber.obj U)
    (f : U ⟶ X) :
    Sigma.ι (fun _ : (yoneda.obj X).obj (op U) ↦ ModuleCat.of R R) f ≫
      Φ.toPresheafFiber U u (Presheaf.freeYoneda X (ModuleCat.of R R)) ≫
        Φ.presheafFiberFreeYonedaDesc R X =
      (ModuleCat.ofHom (Finsupp.lsingle (Φ.fiber.map f u)) :
        ModuleCat.of R R ⟶ ModuleCat.of R (Φ.fiber.obj X →₀ R)) := by
  simp only [presheafFiberFreeYonedaDesc, toPresheafFiber_presheafFiberDesc, Sigma.ι_comp_desc]

/-- The map from the free module on `Φ.fiber.obj X` to the fibre of the free presheaf `R[X]`,
sending `x` to the germ at `(X, x)` of the generator. -/
noncomputable def presheafFiberFreeYonedaLift (X : C) :
    ModuleCat.of R (Φ.fiber.obj X →₀ R) ⟶
      Φ.presheafFiber.obj (Presheaf.freeYoneda X (ModuleCat.of R R)) :=
  ModuleCat.ofHom (Finsupp.linearCombination R fun x ↦
    (Φ.toPresheafFiber X x (Presheaf.freeYoneda X (ModuleCat.of R R))).hom (freeYonedaGen R X))

set_option backward.isDefEq.respectTransparency false in
/-- The fibre of the free presheaf `R[X]` at a point `Φ` is the free `R`-module on
`Φ.fiber.obj X`. -/
noncomputable def presheafFiberFreeYonedaIso (X : C) :
    Φ.presheafFiber.obj (Presheaf.freeYoneda X (ModuleCat.of R R)) ≅
      ModuleCat.of R (Φ.fiber.obj X →₀ R) where
  hom := Φ.presheafFiberFreeYonedaDesc R X
  inv := Φ.presheafFiberFreeYonedaLift R X
  hom_inv_id := by
    refine Φ.presheafFiber_hom_ext fun U u ↦ Sigma.hom_ext _ _ fun f ↦ ?_
    have := ConcreteCategory.congr_hom
      (Φ.ι_toPresheafFiber_presheafFiberFreeYonedaDesc R X U u f) (1 : R)
    simp only [ModuleCat.hom_comp, ModuleCat.hom_ofHom, LinearMap.comp_apply] at this
    ext
    simp only [ModuleCat.hom_comp, LinearMap.comp_apply, this, Category.comp_id]
    simp only [presheafFiberFreeYonedaLift, ModuleCat.hom_ofHom, Finsupp.lsingle_apply]
    erw [Finsupp.linearCombination_single, one_smul]
    rw [← freeYoneda_map_freeYonedaGen R X U f]
    exact (Φ.toPresheafFiber_w_apply f u (Presheaf.freeYoneda X (ModuleCat.of R R))
      (freeYonedaGen R X)).symm
  inv_hom_id := by
    ext x : 2
    refine LinearMap.ext_ring ?_
    have := ConcreteCategory.congr_hom
      (Φ.ι_toPresheafFiber_presheafFiberFreeYonedaDesc R X X x (𝟙 X)) (1 : R)
    simp only [ModuleCat.hom_comp, ModuleCat.hom_ofHom] at this
    simp only [presheafFiberFreeYonedaLift, ModuleCat.hom_comp, ModuleCat.hom_ofHom,
      LinearMap.comp_apply, Finsupp.lsingle_apply]
    erw [Finsupp.linearCombination_single]
    rw [one_smul]
    refine this.trans ?_
    simp

/-- The basis element `x` corresponds to the germ at `(X, x)` of the generator. -/
lemma presheafFiberFreeYonedaIso_inv_single (X : C) (x : Φ.fiber.obj X) :
    (Φ.presheafFiberFreeYonedaIso R X).inv.hom (Finsupp.single x 1) =
      (Φ.toPresheafFiber X x (Presheaf.freeYoneda X (ModuleCat.of R R))).hom
        (freeYonedaGen R X) := by
  simp only [presheafFiberFreeYonedaIso, presheafFiberFreeYonedaLift]
  erw [Finsupp.linearCombination_single, one_smul]

variable [HasWeakSheafify J (ModuleCat.{u + 1} R)] [HasLimitsOfSize.{u, u} (ModuleCat.{u + 1} R)]

/-- The generator of the free sheaf `R[X]` over `X`: the image of `𝟙 X`. -/
noncomputable def sheafFreeYonedaGen (X : C) :
    (Sheaf.freeYoneda J X (ModuleCat.of R R)).obj.obj (op X) :=
  ((CategoryTheory.toSheafify J (Presheaf.freeYoneda X (ModuleCat.of R R))).app (op X)).hom
    (freeYonedaGen R X)

/-- The fibre of the free sheaf `R[X]` at a point `Φ` is the free `R`-module on the fibre
`Φ.fiber.obj X`, the basis element `x` being the germ at `(X, x)` of the generator. -/
noncomputable def sheafFiberFreeYonedaEquiv (X : C) :
    (Φ.fiber.obj X →₀ R) ≃ₗ[R]
      (Φ.sheafFiber (A := ModuleCat.{u + 1} R)).obj (Sheaf.freeYoneda J X (ModuleCat.of R R)) :=
  ((Φ.presheafFiberFreeYonedaIso R X).symm ≪≫
    ((Φ.presheafToSheafCompSheafFiberIso (ModuleCat.{u + 1} R)).app
      (Presheaf.freeYoneda X (ModuleCat.of R R))).symm).toLinearEquiv

set_option backward.isDefEq.respectTransparency false in
/-- The basis element `x` corresponds to the germ at `(X, x)` of the generator. -/
lemma sheafFiberFreeYonedaEquiv_single (X : C) (x : Φ.fiber.obj X) :
    Φ.sheafFiberFreeYonedaEquiv R X (Finsupp.single x 1) =
      (Φ.toPresheafFiber X x (Sheaf.freeYoneda J X (ModuleCat.of R R)).obj).hom
        (sheafFreeYonedaGen R X) := by
  have h₁ := congrArg (Φ.presheafFiber.map (CategoryTheory.toSheafify J
    (Presheaf.freeYoneda X (ModuleCat.of R R)))).hom
    (Φ.presheafFiberFreeYonedaIso_inv_single R X x)
  exact h₁.trans (Φ.toPresheafFiber_naturality_apply _ X x (freeYonedaGen R X))

end CategoryTheory.GrothendieckTopology.Point
