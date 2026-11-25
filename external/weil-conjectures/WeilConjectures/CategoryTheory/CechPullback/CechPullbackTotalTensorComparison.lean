/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import Mathlib.Algebra.Homology.Monoidal
public import Mathlib.CategoryTheory.Abelian.Basic
public import Mathlib.CategoryTheory.Monoidal.Preadditive
public import WeilConjectures.Algebra.Homology.CanonicalRingedTensorComparison.RingedTopoiCanonicalTensorPullbackSupplement

/-! # Total tensor comparison and its augmentation
Source: Stacks Project, sites-modules.tex, Tag 03EL.
-/
@[expose] public noncomputable section
set_option autoImplicit false
universe u v u' v'
open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory
namespace CategoryTheory.CechPullback
variable {A : Type u} [Category.{v} A] [Abelian A] [MonoidalCategory A]
  {B : Type u'} [Category.{v'} B] [Abelian B] [MonoidalCategory B]
  [MonoidalPreadditive A] [MonoidalPreadditive B]
  [HasCoproducts.{0} A] [HasCoproducts.{0} B]
  (F : A ⥤ B) [F.Additive]
  (t : ∀ X Y : A, F.obj (X ⊗ Y) ≅ F.obj X ⊗ F.obj Y)
  (ht : ∀ {X X' Y Y' : A} (f : X ⟶ X') (g : Y ⟶ Y'),
    F.map (f ⊗ₘ g) ≫ (t X' Y').hom =
      (t X Y).hom ≫ (F.map f ⊗ₘ F.map g))

/-- The total inverse comparison is natural in both complex variables.
Source: Stacks Project, sites-modules.tex, Tag 03EL.
Proof: check each totalization summand, use coefficient naturality for the inverse
comparison, and then use naturality of the summand inclusions.
(blueprint: lem-weil-pbc-cech-pullback-total-tensor-comparison) -/
theorem inverse_naturality
    {P P' Q Q' : CochainComplex A ℤ} (f : P ⟶ P') (g : Q ⟶ Q') :
    HomologicalComplex.tensorHom ((F.mapHomologicalComplex (.up ℤ)).map f)
      ((F.mapHomologicalComplex (.up ℤ)).map g) ≫ tensorPullbackTotal F t ht P' Q' =
      tensorPullbackTotal F t ht P Q ≫ (F.mapHomologicalComplex (.up ℤ)).map
        (HomologicalComplex.tensorHom f g) := by
  have hi {X X' Y Y' : A} (a : X ⟶ X') (b : Y ⟶ Y') :
      (F.map a ⊗ₘ F.map b) ≫ (t X' Y').inv =
        (t X Y).inv ≫ F.map (a ⊗ₘ b) := by
    apply (cancel_mono (t X' Y').hom).1
    simp only [Category.assoc, Iso.inv_hom_id, Category.comp_id]
    rw [ht, Iso.inv_hom_id_assoc]
  apply HomologicalComplex.Hom.ext
  funext n
  apply HomologicalComplex.mapBifunctor.hom_ext
  intro a b hab
  simp only [HomologicalComplex.comp_f, tensorPullbackTotal,
    HomologicalComplex.ι_mapBifunctorMap_assoc, tensorPullbackTotalComponent,
    HomologicalComplex.ι_mapBifunctorDesc_assoc, HomologicalComplex.ι_mapBifunctorDesc]
  simp only [Category.assoc]
  change (F.map (f.f a) ▷ F.obj (Q.X b)) ≫
    (F.obj (P'.X a) ◁ F.map (g.f b)) ≫ _ = _
  rw [← tensorHom_def_assoc]
  change (F.map (f.f a) ⊗ₘ F.map (g.f b)) ≫ (t (P'.X a) (Q'.X b)).inv ≫
      F.map (CochainComplex.ιMapBifunctor P' Q' (curriedTensor A) a b n hab) =
    (t (P.X a) (Q.X b)).inv ≫
      F.map (CochainComplex.ιMapBifunctor P Q (curriedTensor A) a b n hab) ≫
        F.map ((HomologicalComplex.mapBifunctorMap f g (curriedTensor A) (.up ℤ)).f n)
  rw [← Category.assoc, hi, Category.assoc, ← F.map_comp]
  congr 2
  rw [← F.map_comp]
  congr 1
  rw [HomologicalComplex.ι_mapBifunctorMap]
  rw [tensorHom_def, Category.assoc]
  rfl

omit [HasCoproducts.{0} B] in
/-- The left unitor on the summand with first degree zero.
Source: Stacks Project, sites-modules.tex, Tag 03EL.
Proof: multiply the inverse-unitor formula by the unitor and cancel the ordinary unit
identification and inverse ordinary unitor.
(blueprint: lem-weil-pbc-cech-pullback-total-tensor-comparison) -/
theorem inclusion_leftUnitor (K : CochainComplex B ℤ) (n : ℤ) :
    HomologicalComplex.ιTensorObj (HomologicalComplex.tensorUnit B (.up ℤ)) K
        0 n n (zero_add n) ≫ (HomologicalComplex.leftUnitor K).hom.f n =
      ((HomologicalComplex.singleObjXSelf (.up ℤ) 0 (𝟙_ B)).hom ▷ K.X n) ≫
        (λ_ (K.X n)).hom := by
  let z := HomologicalComplex.singleObjXSelf (.up ℤ) 0 (𝟙_ B)
  apply (cancel_epi ((λ_ (K.X n)).inv ≫ (z.inv ▷ K.X n))).1
  have hi : (HomologicalComplex.leftUnitor K).inv.f n =
      (λ_ (K.X n)).inv ≫ (z.inv ▷ K.X n) ≫
        HomologicalComplex.ιTensorObj (HomologicalComplex.tensorUnit B (.up ℤ)) K
          0 n n (zero_add n) := HomologicalComplex.leftUnitor'_inv K n
  have hh := congrArg (fun f : K ⟶ K ↦ f.f n)
    (HomologicalComplex.leftUnitor K).inv_hom_id
  simp only [HomologicalComplex.comp_f, HomologicalComplex.id_f, hi,
    Category.assoc] at hh
  simp only [Category.assoc]
  rw [hh]
  simp [← Category.assoc]

/-- The normalized comparison preserves the multiplication of degree-zero units.
Source: Stacks Project, algebraization.tex, Tags 0996 and 099E; sites-modules.tex, Tag 03EL.
Proof: use extensionality into the degree-zero single complex and test on every source
summand. A nonzero first degree makes the tensor summand zero; otherwise both degrees
are zero. The summand formula for the unitor, naturality of the ordinary left unitor,
and the coefficient comparison unit equation give the remaining equality.
(blueprint: lem-weil-pbc-cech-pullback-total-tensor-comparison) -/
theorem inverse_unit (e : F.obj (𝟙_ A) ≅ 𝟙_ B)
    (hu : (t (𝟙_ A) (𝟙_ A)).hom ≫ (e.hom ⊗ₘ e.hom) ≫ (λ_ (𝟙_ B)).hom =
      F.map (λ_ (𝟙_ A)).hom ≫ e.hom) :
    let U := HomologicalComplex.tensorUnit A (.up ℤ)
    let V := HomologicalComplex.tensorUnit B (.up ℤ)
    let e₀ := (HomologicalComplex.singleMapHomologicalComplex F (.up ℤ) 0).app (𝟙_ A) ≪≫
      (HomologicalComplex.single B (.up ℤ) 0).mapIso e
    HomologicalComplex.tensorHom e₀.hom e₀.hom ≫ (HomologicalComplex.leftUnitor V).hom =
      tensorPullbackTotal F t ht U U ≫
        (F.mapHomologicalComplex (.up ℤ)).map (HomologicalComplex.leftUnitor U).hom ≫
        e₀.hom := by
  dsimp only
  apply HomologicalComplex.to_single_hom_ext
  simp only [HomologicalComplex.comp_f, Functor.mapHomologicalComplex_map_f]
  apply HomologicalComplex.mapBifunctor.hom_ext
  intro a b hab
  by_cases ha : a = 0
  · subst a
    have hb : b = 0 := by change 0 + b = 0 at hab; omega
    subst b
    simp only [HomologicalComplex.ι_mapBifunctorMap_assoc,
      tensorPullbackTotal, tensorPullbackTotalComponent,
      HomologicalComplex.ι_mapBifunctorDesc_assoc,
      Iso.trans_hom, Iso.app_hom, Functor.mapIso_hom,
      HomologicalComplex.comp_f,
      HomologicalComplex.singleMapHomologicalComplex_hom_app_self,
      HomologicalComplex.single_map_f_self]
    simp only [Category.assoc, Iso.inv_hom_id_assoc,
      curriedTensor_map_app, curriedTensor_obj_map]
    rw [← tensorHom_def_assoc, inclusion_leftUnitor]
    rw [← F.map_comp_assoc, inclusion_leftUnitor]
    let zA := HomologicalComplex.singleObjXSelf (.up ℤ) 0 (𝟙_ A)
    let zB := HomologicalComplex.singleObjXSelf (.up ℤ) 0 (𝟙_ B)
    change ((F.map zA.hom ≫ e.hom ≫ zB.inv) ⊗ₘ
        (F.map zA.hom ≫ e.hom ≫ zB.inv)) ≫
        (zB.hom ▷ _) ≫ (λ_ _).hom =
      (t _ _).inv ≫ F.map ((zA.hom ▷ _) ≫ (λ_ _).hom) ≫
        F.map zA.hom ≫ e.hom ≫ zB.inv
    apply (cancel_mono zB.hom).1
    simp only [Category.assoc, Iso.inv_hom_id, Category.comp_id]
    rw [← leftUnitor_naturality, ← tensorHom_def_assoc,
      tensorHom_comp_tensorHom_assoc]
    simp only [Category.assoc, Iso.inv_hom_id, Category.comp_id]
    rw [← F.map_comp_assoc]
    simp only [Category.assoc]
    rw [← leftUnitor_naturality, ← tensorHom_def_assoc]
    rw [F.map_comp]
    rw [← tensorHom_comp_tensorHom_assoc]
    apply (cancel_epi (t _ _).hom).1
    simp only [Category.assoc, Iso.hom_inv_id_assoc]
    rw [← Category.assoc, ← ht zA.hom zA.hom]
    simp only [Category.assoc]
    rw [hu]
  · have hz := F.map_isZero
      (HomologicalComplex.isZero_single_obj_X (.up ℤ) 0 (𝟙_ A) a ha)
    exact (((curriedTensor B).flip.obj
      (F.obj ((HomologicalComplex.tensorUnit A (.up ℤ)).X b))).map_isZero hz).eq_of_src _ _
end CategoryTheory.CechPullback
