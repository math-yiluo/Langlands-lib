/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import Mathlib.Algebra.Homology.Monoidal
public import Mathlib.Algebra.Homology.Additive
public import Mathlib.CategoryTheory.Monoidal.Closed.Basic
public import Mathlib.CategoryTheory.Monoidal.Closed.Braided
public import Mathlib.CategoryTheory.Monoidal.Braided.Basic
public import Mathlib.CategoryTheory.Monoidal.Preadditive
public import Mathlib.CategoryTheory.Abelian.Basic
import WeilConjectures.CategoryTheory.CechPullback.CechPullbackTotalTensorComparison

/-! # Tensor comparison of augmented cochain complexes
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
  [SymmetricCategory B] [MonoidalClosed B]
  (F : A ⥤ B) [F.Additive]
  (t : ∀ X Y : A, F.obj (X ⊗ Y) ≅ F.obj X ⊗ F.obj Y)
  (ht : ∀ {X X' Y Y' : A} (f : X ⟶ X') (g : Y ⟶ Y'),
    F.map (f ⊗ₘ g) ≫ (t X' Y').hom =
      (t X Y).hom ≫ (F.map f ⊗ₘ F.map g))

include ht in
/-- Tensor products of comparisons preserving their augmentations also preserve augmentation.
Proof: totalization preserves the coefficient comparison because F is a left adjoint.
Naturality moves both augmentations through it. The two factor equations reduce the
assertion to the comparison of degree-zero units.
Source: Stacks Project, algebraization.tex, Tags 0996 and 099E; sites-modules.tex, Tag 03EL.
(blueprint: lem-weil-pbc-cech-pullback-augmented-tensor-comparison) -/
theorem augmented_tensor (G : B ⥤ A) (adj : F ⊣ G)
    (e : F.obj (𝟙_ A) ≅ 𝟙_ B)
    (hu : (t (𝟙_ A) (𝟙_ A)).hom ≫ (e.hom ⊗ₘ e.hom) ≫ (λ_ (𝟙_ B)).hom =
      F.map (λ_ (𝟙_ A)).hom ≫ e.hom)
    (P Q : CochainComplex A ℤ) (P' Q' : CochainComplex B ℤ)
    (a : P ⟶ HomologicalComplex.tensorUnit A (.up ℤ))
    (b : Q ⟶ HomologicalComplex.tensorUnit A (.up ℤ))
    (a' : P' ⟶ HomologicalComplex.tensorUnit B (.up ℤ))
    (b' : Q' ⟶ HomologicalComplex.tensorUnit B (.up ℤ))
    (lx : (F.mapHomologicalComplex (.up ℤ)).obj P ≅ P')
    (ly : (F.mapHomologicalComplex (.up ℤ)).obj Q ≅ Q')
    (hx : lx.hom ≫ a' = (F.mapHomologicalComplex (.up ℤ)).map a ≫
      (HomologicalComplex.singleMapHomologicalComplex F (.up ℤ) 0).hom.app (𝟙_ A) ≫
        (HomologicalComplex.single B (.up ℤ) 0).map e.hom)
    (hy : ly.hom ≫ b' = (F.mapHomologicalComplex (.up ℤ)).map b ≫
      (HomologicalComplex.singleMapHomologicalComplex F (.up ℤ) 0).hom.app (𝟙_ A) ≫
        (HomologicalComplex.single B (.up ℤ) 0).map e.hom) :
    ∃ l : (F.mapHomologicalComplex (.up ℤ)).obj (HomologicalComplex.tensorObj P Q) ≅
        HomologicalComplex.tensorObj P' Q',
      l.hom ≫ HomologicalComplex.tensorHom a' b' ≫
          (HomologicalComplex.leftUnitor (HomologicalComplex.tensorUnit B (.up ℤ))).hom =
        (F.mapHomologicalComplex (.up ℤ)).map (HomologicalComplex.tensorHom a b ≫
          (HomologicalComplex.leftUnitor (HomologicalComplex.tensorUnit A (.up ℤ))).hom) ≫
          (HomologicalComplex.singleMapHomologicalComplex F (.up ℤ) 0).hom.app (𝟙_ A) ≫
            (HomologicalComplex.single B (.up ℤ) 0).map e.hom := by
  have := tensorPullbackTotal_isIso F t ht G adj P Q
  let k := asIso (tensorPullbackTotal F t ht P Q)
  refine ⟨k.symm ≪≫ tensorIso lx ly, ?_⟩
  apply (cancel_epi k.hom).1
  simp only [Iso.trans_hom, Iso.symm_hom, tensorIso_hom, Category.assoc,
    Iso.hom_inv_id_assoc]
  change (lx.hom ⊗ₘ ly.hom) ≫ (a' ⊗ₘ b') ≫ _ = _
  rw [tensorHom_comp_tensorHom_assoc, hx, hy]
  let e₀ := (HomologicalComplex.singleMapHomologicalComplex F (.up ℤ) 0).app (𝟙_ A) ≪≫
    (HomologicalComplex.single B (.up ℤ) 0).mapIso e
  change ((_ ≫ e₀.hom) ⊗ₘ (_ ≫ e₀.hom)) ≫ _ = _
  rw [← tensorHom_comp_tensorHom_assoc]
  have he := inverse_unit F t ht e hu
  change (e₀.hom ⊗ₘ e₀.hom) ≫
      (HomologicalComplex.leftUnitor (HomologicalComplex.tensorUnit B (.up ℤ))).hom = _ at he
  rw [he]
  have hn := inverse_naturality F t ht a b
  change ((F.mapHomologicalComplex (.up ℤ)).map a ⊗ₘ
      (F.mapHomologicalComplex (.up ℤ)).map b) ≫ _ = _ at hn
  rw [← Category.assoc, hn]
  simp only [Functor.map_comp, Category.assoc, k, asIso_hom, Iso.trans_hom, Iso.app_hom,
    Functor.mapIso_hom]
end CategoryTheory.CechPullback
