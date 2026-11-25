/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.CategoryTheory.Sites.CechComplexFunctor
public import Mathlib.CategoryTheory.Abelian.Basic
public import Mathlib.CategoryTheory.Preadditive.Injective.Basic
public import Mathlib.Algebra.Homology.ShortComplex.HomologicalComplex
import WeilConjectures.CategoryTheory.Sites.CechComplex
import Mathlib.CategoryTheory.Preadditive.Yoneda.Basic

/-! # Positive Čech exactness of injective categorical presheaves

Source: Stacks Project, Tag 03AW; the cofree contraction works in any abelian
coefficient category with the indicated products.
-/

@[expose] public section

universe u' u

open CategoryTheory Limits Opposite

namespace CategoryTheory.Presheaf

set_option backward.isDefEq.respectTransparency false

variable {C : Type (u + 1)} [Category.{u} C]
  {A : Type u'} [Category.{u + 1} A] [Abelian A] [HasProducts.{u + 1} A] [HasProducts.{0} A]
  (P : Cᵒᵖ ⥤ A)

/-- The product of the right adjoints of evaluation at every object. -/
private noncomputable def categoricalCofree : Cᵒᵖ ⥤ A where
  obj Y := ∏ᶜ fun s : Σ Z : C, Z ⟶ Y.unop ↦ P.obj (op s.1)
  map {Y Y'} h := Pi.lift fun s : Σ Z : C, Z ⟶ Y'.unop ↦
    Pi.π (fun t : Σ Z : C, Z ⟶ Y.unop ↦ P.obj (op t.1)) ⟨s.1, s.2 ≫ h.unop⟩
  map_id Y := by
    apply Pi.hom_ext
    rintro ⟨Z, g⟩
    erw [Pi.lift_comp_π, Category.id_comp]
    dsimp only [unop_id]
    rw [Category.comp_id]
  map_comp h h' := by
    apply Pi.hom_ext
    rintro ⟨Z, g⟩
    simp only [Category.assoc]
    erw [Pi.lift_comp_π, Pi.lift_comp_π, Pi.lift_comp_π]
    dsimp only [Sigma.fst, Sigma.snd]
    rw [unop_comp, Category.assoc]

/-- Restriction of a section to all arrows into its object. -/
private noncomputable def toCategoricalCofree : P ⟶ categoricalCofree P where
  app Y := Pi.lift fun s ↦ P.map s.2.op
  naturality Y Y' h := by
    apply Pi.hom_ext
    rintro ⟨Z, g⟩
    dsimp only [categoricalCofree]
    simp only [Category.assoc]
    erw [Pi.lift_comp_π, Pi.lift_comp_π, Pi.lift_comp_π]
    rw [op_comp, P.map_comp]
    rfl

private instance mono_toCategoricalCofree : Mono (toCategoricalCofree P) := by
  have (Y : Cᵒᵖ) : Mono ((toCategoricalCofree P).app Y) := by
    have h : (toCategoricalCofree P).app Y ≫
        Pi.π (fun s : Σ Z : C, Z ⟶ Y.unop ↦ P.obj (op s.1)) ⟨Y.unop, 𝟙 _⟩ =
        𝟙 (P.obj Y) := by
      dsimp only [toCategoricalCofree]
      erw [Pi.lift_comp_π]
      simp
    exact mono_of_mono_fac h
  exact NatTrans.mono_of_mono_app _

/-- Taking morphisms into the categorical cofree object gives the ordinary cofree
abelian presheaf. -/
private noncomputable def categoricalCofreeHomIso (B : A) :
    categoricalCofree P ⋙ preadditiveCoyoneda.obj (op B) ≅
      cofree (P ⋙ preadditiveCoyoneda.obj (op B)) :=
  NatIso.ofComponents (fun Y ↦ AddEquiv.toAddCommGrpIso
    { toFun := fun f Z g ↦ f ≫
        Pi.π (fun s : Σ T : C, T ⟶ Y.unop ↦ P.obj (op s.1)) ⟨Z, g⟩
      invFun := fun f ↦ Pi.lift fun s ↦ f s.1 s.2
      left_inv := fun f ↦ by
        apply Pi.hom_ext
        intro s
        erw [Pi.lift_comp_π]
      right_inv := fun f ↦ by
        change (∀ (Z : C) (_ : Z ⟶ Y.unop), B ⟶ P.obj (op Z)) at f
        funext Z g
        change (Pi.lift fun s : Σ T : C, T ⟶ Y.unop ↦ f s.1 s.2) ≫
          Pi.π (fun s : Σ T : C, T ⟶ Y.unop ↦ P.obj (op s.1)) ⟨Z, g⟩ = f Z g
        erw [Pi.lift_comp_π]
      map_add' := fun f g ↦ by
        funext Z h
        exact Preadditive.add_comp _ _ _ _ _ _ }) (by
    intro Y Y' h
    apply AddCommGrpCat.ext
    intro f
    funext Z g
    change (f ≫ (categoricalCofree P).map h) ≫
      Pi.π (fun s : Σ T : C, T ⟶ Y'.unop ↦ P.obj (op s.1)) ⟨Z, g⟩ =
      f ≫ Pi.π (fun s : Σ T : C, T ⟶ Y.unop ↦ P.obj (op s.1)) ⟨Z, g ≫ h.unop⟩
    dsimp only [categoricalCofree]
    rw [Category.assoc]
    erw [Pi.lift_comp_π])

variable {V : C} [HasFiniteProducts (Over V)] {n : ℕ} (U : Fin n → Over V)

/-- Morphisms into a categorical Čech complex are ordinary abelian Čech cochains. -/
private noncomputable def categoricalCechHomIso (B : A) :
    ((preadditiveCoyoneda.obj (op B)).mapHomologicalComplex (ComplexShape.up ℕ)).obj
        ((cechComplexFunctor U).obj ((Over.forget V).op ⋙ P)) ≅
      (cechComplex U).obj (P ⋙ preadditiveCoyoneda.obj (op B)) :=
  HomologicalComplex.Hom.isoOfComponents (fun k ↦ AddEquiv.toAddCommGrpIso
    { toFun := fun f y ↦ f ≫ Pi.π _ y
      invFun := fun f ↦ Pi.lift f
      left_inv := fun f ↦ by
        apply Pi.hom_ext
        intro y
        erw [Pi.lift_comp_π]
      right_inv := fun f ↦ by
        funext y
        change Pi.lift f ≫ Pi.π _ y = f y
        erw [Pi.lift_comp_π]
      map_add' := fun f g ↦ by
        funext y
        exact Preadditive.add_comp _ _ _ _ _ _ }) (by
    rintro k l (rfl : k + 1 = l)
    apply AddCommGrpCat.ext
    intro f
    funext y
    symm
    change Fin (k + 2) → Fin n at y
    change (f ≫ ((cechComplexFunctor U).obj ((Over.forget V).op ⋙ P)).d k (k + 1)) ≫
      Pi.π _ y = ((cechComplex U).obj (P ⋙ preadditiveCoyoneda.obj (op B))).d
        k (k + 1) (fun z ↦ f ≫ Pi.π
          (fun t ↦ P.obj (op (cechNerveObj U t).left)) z) y
    rw [cechComplexFunctor_obj_d, Preadditive.comp_sum, Preadditive.sum_comp,
      cechComplex_d_apply]
    apply Finset.sum_congr rfl
    intro i _
    simp only [Preadditive.comp_zsmul, Preadditive.zsmul_comp, Category.assoc]
    erw [Pi.lift_comp_π]
    congr 1
    exact (Category.assoc _ _ _).symm)

omit [HasProducts.{u + 1} A] [HasProducts.{0} A] in
/-- Exactness after every additive representable implies categorical exactness.
Only the representable based at the kernel is needed. -/
private theorem exactAt_of_preadditiveCoyoneda (K : CochainComplex A ℕ) (q : ℕ)
    (h : ∀ B : A,
      (((preadditiveCoyoneda.obj (op B)).mapHomologicalComplex (ComplexShape.up ℕ)).obj K).ExactAt
        (q + 1)) : K.ExactAt (q + 1) := by
  let T := K.sc' q (q + 1) (q + 2)
  have hT := h (kernel T.g)
  rw [HomologicalComplex.exactAt_iff' _ q (q + 1) (q + 2) (by simp) (by simp),
    ShortComplex.ab_exact_iff] at hT
  obtain ⟨b, hb⟩ := hT (kernel.ι T.g) (by
    change kernel.ι T.g ≫ T.g = 0
    exact kernel.condition _)
  rw [HomologicalComplex.exactAt_iff' K q (q + 1) (q + 2) (by simp) (by simp)]
  change T.Exact
  rw [ShortComplex.exact_iff_epi_kernel_lift]
  have he : b ≫ kernel.lift T.g T.f T.zero = 𝟙 _ := by
    apply (cancel_mono (kernel.ι T.g)).1
    rw [Category.assoc, kernel.lift_ι, Category.id_comp]
    exact hb
  exact epi_of_epi_fac he

/-- The cofree categorical Čech complex is exact in positive degrees. Its image
under every additive representable has the usual insertion contraction. -/
private theorem exactAt_categoricalCech_cofree (q : ℕ) :
    ((cechComplexFunctor U).obj
      ((Over.forget V).op ⋙ categoricalCofree P)).ExactAt (q + 1) := by
  apply exactAt_of_preadditiveCoyoneda
  intro B
  have h := exactAt_cechComplex_cofree U (P ⋙ preadditiveCoyoneda.obj (op B)) q
  let e := categoricalCechHomIso (categoricalCofree P) U B ≪≫
    (cechComplex U).mapIso (categoricalCofreeHomIso P B)
  exact h.of_iso e.symm

/-- An injective categorical presheaf is a retract of its cofree presheaf, so its
finite Čech complex is exact in every positive degree.
Source: Stacks Project, Tag 03AW, and the cofree insertion contraction.
(blueprint: stage3-categorical-injective-cech-exactness).

Proof: Restrict sections along every arrow into an object to embed the presheaf
in the product of the right adjoints of the evaluation functors. Evaluation at
its identity arrow splits this map objectwise, so it is a monomorphism. Injectivity
splits it as a map of presheaves. After taking morphisms from any coefficient
object, the cofree Čech complex becomes the ordinary abelian cofree Čech complex;
inserting a chosen lift depending only on the composite arrow into the covered
object contracts its positive degrees. Apply this with the kernel of a differential
to obtain categorical exactness. Finally the split presheaf maps induce split maps
on Čech homology, and a retract of a zero object is zero. This also treats the empty
family, whose positive Čech terms are zero. -/
theorem exactAt_categoricalCech_of_injective [Injective P] (q : ℕ) :
    ((cechComplexFunctor U).obj ((Over.forget V).op ⋙ P)).ExactAt (q + 1) := by
  let T := (Functor.whiskeringLeft (Over V)ᵒᵖ Cᵒᵖ A).obj (Over.forget V).op ⋙
    cechComplexFunctor U
  let H := HomologicalComplex.homologyFunctor A (ComplexShape.up ℕ) (q + 1)
  let ι' := T.map (toCategoricalCofree P)
  let ρ := T.map (Injective.factorThru (𝟙 P) (toCategoricalCofree P))
  have hr : ι' ≫ ρ = 𝟙 _ := by
    dsimp only [ι', ρ]
    rw [← T.map_comp, Injective.comp_factorThru, T.map_id]
  have hh : H.map ι' ≫ H.map ρ = 𝟙 _ := by
    rw [← H.map_comp, hr, H.map_id]
  have hz : IsZero (H.obj (T.obj (categoricalCofree P))) :=
    (exactAt_categoricalCech_cofree P U q).isZero_homology
  rw [HomologicalComplex.exactAt_iff_isZero_homology, IsZero.iff_id_eq_zero]
  change 𝟙 (H.obj (T.obj P)) = 0
  rw [← hh, hz.eq_of_src (H.map ρ) 0, comp_zero]

end CategoryTheory.Presheaf
