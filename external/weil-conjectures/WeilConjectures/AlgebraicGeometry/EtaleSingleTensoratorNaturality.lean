/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module
public import WeilConjectures.SixFunctors.Etale.Derived.Invertible

/-! # Naturality of the canonical degree-zero tensor comparison -/

@[expose] public section

set_option autoImplicit false
set_option backward.defeqAttrib.useBackward true

universe u uB
open CategoryTheory MonoidalCategory

namespace AlgebraicGeometry.Etale

attribute [local instance] SymmetricCategory.toBraidedCategory
attribute [local instance] sheafMonoidalCategory sheafBraidedCategory sheafMonoidalClosed

variable {B : Type uB} [Category.{u + 1} B] [Abelian B]
  [IsGrothendieckAbelian.{u + 1} B] [MonoidalCategory B] [MonoidalPreadditive B]
  [SymmetricCategory B] [MonoidalClosed B] [Abelian.HasFunctorialFlatResolution B]
  {X : AlgebraicGeometry.Scheme.{u}}

section Cochain

variable {C : Type uB} [Category.{u + 1} C] [Abelian C]
  [IsGrothendieckAbelian.{u + 1} C] [MonoidalCategory C] [MonoidalPreadditive C]
  [SymmetricCategory C] [MonoidalClosed C]

@[irreducible]
private noncomputable def cochainSingleTensorIso
    (L M : C) :
    (HomologicalComplex.single _ (.up ℤ) 0).obj L ⊗
      (HomologicalComplex.single _ (.up ℤ) 0).obj M ≅
        (HomologicalComplex.single _ (.up ℤ) 0).obj (L ⊗ M) :=
  ((CochainComplex.map₂HomologicalComplexObjSingleIso (curriedTensor _) L).app
    ((HomologicalComplex.single _ (.up ℤ) 0).obj M)) ≪≫
    ((HomologicalComplex.singleMapHomologicalComplex (tensorLeft L) (.up ℤ) 0).app M)

private lemma cochainSingleTensorIso_inv_f (L M : C) :
    (cochainSingleTensorIso L M).inv.f 0 =
      HomologicalComplex.ιTensorObj
        ((HomologicalComplex.single _ (.up ℤ) 0).obj L)
        ((HomologicalComplex.single _ (.up ℤ) 0).obj M) 0 0 0 rfl := by
  simp [cochainSingleTensorIso, CochainComplex.mapBifunctorSingle₁Iso_inv_f,
    HomologicalComplex.singleMapHomologicalComplex_inv_app_self,
    HomologicalComplex.singleObjXSelf, HomologicalComplex.singleObjXIsoOfEq,
    HomologicalComplex.single, whiskerLeft_id]

private lemma cochainSingleTensorIso_naturality
    {L L' M M' : C} (f : L ⟶ L') (g : M ⟶ M') :
    ((HomologicalComplex.single _ (.up ℤ) 0).map f ⊗ₘ
        (HomologicalComplex.single _ (.up ℤ) 0).map g) ≫
      (cochainSingleTensorIso L' M').hom =
    (cochainSingleTensorIso L M).hom ≫
      (HomologicalComplex.single _ (.up ℤ) 0).map (f ⊗ₘ g) := by
  apply (cancel_epi (cochainSingleTensorIso L M).inv).1
  simp only [Iso.inv_hom_id_assoc]
  apply (cancel_mono (cochainSingleTensorIso L' M').inv).1
  simp only [Category.assoc, Iso.hom_inv_id, Category.comp_id]
  apply HomologicalComplex.from_single_hom_ext
  simp only [HomologicalComplex.comp_f, cochainSingleTensorIso_inv_f]
  simp only [tensorHom_def, HomologicalComplex.comp_f]
  erw [CochainComplex.Monoidal.ι_whiskerRight_assoc,
    CochainComplex.ιTensorObj_whiskerLeft_f]
  simp [HomologicalComplex.single, Category.assoc]

end Cochain

@[irreducible]
private noncomputable def singleIsoQh :
    DerivedCategory.singleFunctor (Sheaf X.smallEtaleTopology B) 0 ≅
      HomologicalComplex.single _ (.up ℤ) 0 ⋙ HomotopyCategory.quotient _ (.up ℤ) ⋙
        DerivedCategory.Qh :=
  DerivedCategory.singleFunctorIsoCompQ _ 0 ≪≫
    Functor.isoWhiskerLeft _ (DerivedCategory.quotientCompQhIso _).symm

/-- Naturality in both sheaves of the specified flat degree-zero tensor comparison.
Source: the tensor localization construction of Stacks Tag 06YU.
(auxiliary; not a blueprint node).
Proof: the single-complex tensor comparison is natural on its sole nonzero summand.
Compose its naturality with those of the homotopy quotient and Qh tensorators,
and then with the natural single/quotient comparison. The flatness proofs only
supply invertibility, and do not change the underlying morphisms. -/
theorem singleFunctorObjTensorIso_hom_naturality
    {L L' M M' : Sheaf X.smallEtaleTopology B} (f : L ⟶ L') (g : M ⟶ M')
    (hL : ObjectProperty.flat L) (hL' : ObjectProperty.flat L') :
    ((DerivedCategory.singleFunctor _ 0).map f ⊗ₘ
        (DerivedCategory.singleFunctor _ 0).map g) ≫
      (singleFunctorObjTensorIso L' M' hL').hom =
    (singleFunctorObjTensorIso L M hL).hom ≫
      (DerivedCategory.singleFunctor _ 0).map (f ⊗ₘ g) := by
  let sg := HomologicalComplex.single (Sheaf X.smallEtaleTopology B) (.up ℤ) 0
  let F := HomotopyCategory.quotient (Sheaf X.smallEtaleTopology B) (.up ℤ) ⋙
    DerivedCategory.Qh
  let e := singleIsoQh (B := B) (X := X)
  have fac (A C : Sheaf X.smallEtaleTopology B) (hA : ObjectProperty.flat A) :
      (singleFunctorObjTensorIso A C hA).hom =
        (e.hom.app A ⊗ₘ e.hom.app C) ≫
          Functor.LaxMonoidal.μ F (sg.obj A) (sg.obj C) ≫
          F.map (cochainSingleTensorIso A C).hom ≫ e.inv.app (A ⊗ C) := by
    dsimp [singleFunctorObjTensorIso, singleFunctorObjIsoQh,
      cochainSingleTensorIso, e, singleIsoQh, F, sg]
    simp [cochainSingleTensorIso, singleIsoQh, Functor.map_comp, Category.assoc]
  rw [fac L M hL, fac L' M' hL']
  change (_ ⊗ₘ _) ≫ ((e.hom.app L' ⊗ₘ e.hom.app M') ≫
      Functor.LaxMonoidal.μ F (sg.obj L') (sg.obj M') ≫
      F.map (cochainSingleTensorIso L' M').hom ≫ e.inv.app (L' ⊗ M')) =
    ((e.hom.app L ⊗ₘ e.hom.app M) ≫
      Functor.LaxMonoidal.μ F (sg.obj L) (sg.obj M) ≫
      F.map (cochainSingleTensorIso L M).hom ≫ e.inv.app (L ⊗ M)) ≫ _
  have ne_f : (DerivedCategory.singleFunctor _ 0).map f ≫ e.hom.app L' =
      e.hom.app L ≫ F.map (sg.map f) := e.hom.naturality f
  have ne_g : (DerivedCategory.singleFunctor _ 0).map g ≫ e.hom.app M' =
      e.hom.app M ≫ F.map (sg.map g) := e.hom.naturality g
  simp only [Category.assoc]
  rw [tensorHom_comp_tensorHom_assoc, ne_f, ne_g,
    ← tensorHom_comp_tensorHom_assoc, Functor.LaxMonoidal.μ_natural_assoc F (sg.map f) (sg.map g),
    ← F.map_comp_assoc, cochainSingleTensorIso_naturality, F.map_comp, Category.assoc]
  exact congrArg ((e.hom.app L ⊗ₘ e.hom.app M) ≫
    Functor.LaxMonoidal.μ F (sg.obj L) (sg.obj M) ≫
      F.map (cochainSingleTensorIso L M).hom ≫ ·) (e.inv.naturality (f ⊗ₘ g))

end AlgebraicGeometry.Etale
