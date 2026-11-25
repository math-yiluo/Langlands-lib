/-
Copyright (c) 2026 Nailin Guan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Nailin Guan
-/
module

public import Mathlib.CategoryTheory.Bicategory.End
public import Mathlib.CategoryTheory.Monoidal.Transport
public import WeilConjectures.CategoryTheory.ModuleObjects.Bimod
public import WeilConjectures.CategoryTheory.ModuleObjects.Preadditive

/-!

# The relative tensor product of module objects

Let `C` be a braided monoidal category with coequalizers, such that tensoring on either side
preserves colimits, and let `R : C` be a commutative algebra object. For two `R`-module objects
`M` and `N`, the *relative tensor product* is the coequalizer
```
M ⊗_R N := coequalizer (M ⊗ R ⊗ N ⇉ M ⊗ N),
```
of the right action of `R` on `M` (the braiding followed by the left action) and the left
action of `R` on `N`. It is again an `R`-module object, and this makes `Mod C R` a monoidal
category with unit `R` (`Mod.regular R`).

We obtain this structure from Mathlib's tensor product of bimodules (`Bimod.tensorBimod`): left
module objects over the commutative algebra object `R` are the same as symmetric
`R`-`R`-bimodules (see `WeilConjectures.CategoryTheory.ModuleObjects.Bimod`), symmetric
bimodules are stable under the tensor product, and the monoidal structure on `Mod C R` is
induced along the faithful functor `Mod.toBimod R : Mod C R ⥤ Bimod R R`
(`CategoryTheory.Monoidal.induced`).

The tensor product of a right `R`-module and a left `R`-module over an arbitrary (not
necessarily commutative) algebra object `R` is the special case `Bimod.tensorBimod` of Mathlib,
with right modules being bimodules over `(𝟙, R)` and left modules bimodules over `(R, 𝟙)`.

If moreover `C` is preadditive and its tensor product is additive in each variable, then so is
the relative tensor product (`MonoidalPreadditive (Mod C R)`).

-/

@[expose] public section

universe v u

open CategoryTheory MonoidalCategory BraidedCategory MonObj Limits


variable {C : Type u} [Category.{v} C] [MonoidalCategory C]
  [HasCoequalizers C] [∀ X : C, PreservesColimitsOfSize.{0, 0} (tensorLeft X)]
  [∀ X : C, PreservesColimitsOfSize.{0, 0} (tensorRight X)]

namespace Bimod

/-- The monoidal structure on the bimodules over a monoid object `A`, given by the tensor
product over `A`. It is not an instance, because it is only used to induce the monoidal
structure on module objects over a commutative algebra object. -/
@[instance_reducible]
noncomputable def monoidalCategory (A : Mon C) : MonoidalCategory (Bimod A A) :=
  @instMonoidalCategoryHom (Mon C) monBicategory A

attribute [local instance] monoidalCategory

lemma tensorObj_eq {A : Mon C} (P Q : Bimod A A) : P ⊗ Q = P.tensorBimod Q := rfl

lemma tensorUnit_eq {A : Mon C} : 𝟙_ (Bimod A A) = regular A := rfl

lemma whiskerLeft_eq {A : Mon C} (P : Bimod A A) {Q Q' : Bimod A A} (f : Q ⟶ Q') :
    P ◁ f = whiskerLeft P f := rfl

lemma whiskerRight_eq {A : Mon C} {P P' : Bimod A A} (f : P ⟶ P') (Q : Bimod A A) :
    f ▷ Q = whiskerRight f Q := rfl

lemma associator_eq {A : Mon C} (P Q S : Bimod A A) :
    α_ P Q S = associatorBimod P Q S := rfl

lemma leftUnitor_eq {A : Mon C} (P : Bimod A A) : λ_ P = leftUnitorBimod P := rfl

lemma rightUnitor_eq {A : Mon C} (P : Bimod A A) : ρ_ P = rightUnitorBimod P := rfl

end Bimod

attribute [local instance] Bimod.monoidalCategory

namespace CategoryTheory

namespace Mod

variable [BraidedCategory C] {R : C} [MonObj R] [IsCommMonObj R]

/-- The bimodule associated with the relative tensor product is symmetric. -/
lemma isSymmetric_tensor (M N : Mod C R) :
    ((toBimod R).obj M ⊗ (toBimod R).obj N).IsSymmetric :=
  (Bimod.isSymmetric_toBimodObj M).tensorBimod (Bimod.isSymmetric_toBimodObj N)

/-- The identification of the bimodule associated with the relative tensor product of two module
objects with the tensor product of the associated bimodules. -/
noncomputable def toBimodTensorIso (M N : Mod C R) :
    (toBimod R).obj ((fromBimod R).obj ((toBimod R).obj M ⊗ (toBimod R).obj N)) ≅
      (toBimod R).obj M ⊗ (toBimod R).obj N :=
  (isSymmetric_tensor M N).iso

@[simp]
lemma toBimodTensorIso_hom_hom (M N : Mod C R) : (toBimodTensorIso M N).hom.hom = 𝟙 _ := rfl

@[simp]
lemma toBimodTensorIso_inv_hom (M N : Mod C R) : (toBimodTensorIso M N).inv.hom = 𝟙 _ := rfl

/-- The identification of the bimodule associated with `R` with the regular bimodule. -/
noncomputable def toBimodRegularIso :
    (toBimod R).obj (regular R) ≅ 𝟙_ (Bimod (Mon.mk R) (Mon.mk R)) :=
  (Bimod.isSymmetric_regular (A := Mon.mk R)).iso

@[simp]
lemma toBimodRegularIso_hom_hom : (toBimodRegularIso (R := R)).hom.hom = 𝟙 _ := rfl

@[simp]
lemma toBimodRegularIso_inv_hom : (toBimodRegularIso (R := R)).inv.hom = 𝟙 _ := rfl

noncomputable instance monoidalCategoryStruct : MonoidalCategoryStruct (Mod C R) where
  tensorObj M N := (fromBimod R).obj ((toBimod R).obj M ⊗ (toBimod R).obj N)
  whiskerLeft M _ _ f := (fromBimod R).map ((toBimod R).obj M ◁ (toBimod R).map f)
  whiskerRight f N := (fromBimod R).map ((toBimod R).map f ▷ (toBimod R).obj N)
  tensorUnit := regular R
  associator M N P := (fromBimod R).mapIso
    (whiskerRightIso (toBimodTensorIso M N) _ ≪≫ α_ _ _ _ ≪≫
      whiskerLeftIso _ (toBimodTensorIso N P).symm)
  leftUnitor _ := (fromBimod R).mapIso (whiskerRightIso toBimodRegularIso _ ≪≫ λ_ _)
  rightUnitor _ := (fromBimod R).mapIso (whiskerLeftIso _ toBimodRegularIso ≪≫ ρ_ _)

/-- The data inducing the monoidal structure on `Mod C R` along `toBimod R`. -/
noncomputable def inducingFunctorData :
    Monoidal.InducingFunctorData (toBimod R : Mod C R ⥤ _) where
  μIso M N := (toBimodTensorIso M N).symm
  εIso := toBimodRegularIso.symm
  whiskerLeft_eq M N₁ N₂ f := by
    ext
    exact (Category.comp_id _).symm.trans (Category.id_comp _).symm
  whiskerRight_eq f N := by
    ext
    exact (Category.comp_id _).symm.trans (Category.id_comp _).symm
  tensorHom_eq f g := by
    ext
    exact (Category.comp_id _).symm.trans (Category.id_comp _).symm
  associator_eq M N P := by
    ext
    simp only [toBimod_map_hom, Iso.symm_symm_eq, Iso.trans_assoc, Iso.trans_hom, tensorIso_hom,
      Iso.refl_hom, tensorHom_id, Iso.symm_hom, id_tensorHom, Bimod.comp_hom',
      toBimodTensorIso_inv_hom]
    erw [Category.id_comp, Category.comp_id]
    rfl
  leftUnitor_eq M := by
    ext
    simp only [toBimod_map_hom, Iso.symm_symm_eq, Iso.trans_assoc, Iso.trans_hom, tensorIso_hom,
      Iso.refl_hom, tensorHom_id, Bimod.comp_hom']
    erw [Category.id_comp]
    rfl
  rightUnitor_eq M := by
    ext
    simp only [toBimod_map_hom, Iso.symm_symm_eq, Iso.trans_assoc, Iso.trans_hom, tensorIso_hom,
      Iso.refl_hom, id_tensorHom, Bimod.comp_hom']
    erw [Category.id_comp]
    rfl

/-- The monoidal structure on the module objects over a commutative algebra object `R`, given by
the relative tensor product over `R`. -/
noncomputable instance monoidalCategory : MonoidalCategory (Mod C R) :=
  Monoidal.induced (toBimod R) inducingFunctorData

section TensorProduct

variable (M N : Mod C R)

/-- The relative tensor product `M ⊗_R N` is the coequalizer of the right action of `R` on `M`
and the left action of `R` on `N`. -/
lemma tensorObj_X : (M ⊗ N).X =
    coequalizer (((β_ M.X R).hom ≫ γ[R,M.X]) ▷ N.X) ((α_ M.X R N.X).hom ≫ M.X ◁ γ[R,N.X]) :=
  rfl


/-- The projection `M ⊗ N ⟶ M ⊗_R N`. -/
noncomputable def tensorObjπ : M.X ⊗ N.X ⟶ (M ⊗ N).X :=
  coequalizer.π (((β_ M.X R).hom ≫ γ[R,M.X]) ▷ N.X) ((α_ M.X R N.X).hom ≫ M.X ◁ γ[R,N.X])

@[reassoc]
lemma tensorObjπ_condition :
    ((β_ M.X R).hom ≫ γ[R,M.X]) ▷ N.X ≫ tensorObjπ M N =
      ((α_ M.X R N.X).hom ≫ M.X ◁ γ[R,N.X]) ≫ tensorObjπ M N :=
  coequalizer.condition _ _

/-- `tensorObjπ M N` exhibits `M ⊗_R N` as the coequalizer of the two actions of `R`. -/
noncomputable def isColimitTensorπ :
    IsColimit (Cofork.ofπ (tensorObjπ M N) (tensorObjπ_condition M N) :
      Cofork (((β_ M.X R).hom ≫ γ[R,M.X]) ▷ N.X) ((α_ M.X R N.X).hom ≫ M.X ◁ γ[R,N.X])) :=
  coequalizerIsCoequalizer _ _

instance : Epi (tensorObjπ M N) := by
  dsimp [tensorObjπ]
  infer_instance

/-- The action of `R` on `M ⊗_R N` is induced by the action of `R` on `M`. -/
@[reassoc]
lemma whiskerLeft_tensorπ_smul :
    R ◁ tensorObjπ M N ≫ γ[R,(M ⊗ N).X] = (α_ R M.X N.X).inv ≫ γ[R,M.X] ▷ N.X ≫ tensorObjπ M N :=
  Bimod.TensorBimod.whiskerLeft_π_actLeft ((toBimod R).obj M) ((toBimod R).obj N)

variable {M N}

@[reassoc]
lemma tensorObjπ_whiskerLeft {N' : Mod C R} (f : N ⟶ N') :
    tensorObjπ M N ≫ (M ◁ f).hom = M.X ◁ f.hom ≫ tensorObjπ M N' :=
  ι_colimMap _ _

@[reassoc]
lemma tensorObjπ_whiskerRight {M' : Mod C R} (f : M ⟶ M') :
    tensorObjπ M N ≫ (f ▷ N).hom = f.hom ▷ N.X ≫ tensorObjπ M' N :=
  ι_colimMap _ _

end TensorProduct

section Preadditive

variable [Preadditive C] [MonoidalPreadditive C]

/-- The relative tensor product is additive in each variable. -/
instance : MonoidalPreadditive (Mod C R) where
  whiskerLeft_zero {M _ _} := hom_ext _ _ (by
    rw [← cancel_epi (tensorObjπ _ _), tensorObjπ_whiskerLeft]
    simp)
  zero_whiskerRight {M _ _} := hom_ext _ _ (by
    rw [← cancel_epi (tensorObjπ _ _), tensorObjπ_whiskerRight]
    simp)
  whiskerLeft_add {M _ _} f g := hom_ext _ _ (by
    rw [← cancel_epi (tensorObjπ _ _), tensorObjπ_whiskerLeft]
    simp [Preadditive.comp_add, tensorObjπ_whiskerLeft, Preadditive.add_comp])
  add_whiskerRight f g := hom_ext _ _ (by
    rw [← cancel_epi (tensorObjπ _ _), tensorObjπ_whiskerRight]
    simp [Preadditive.comp_add, tensorObjπ_whiskerRight, Preadditive.add_comp])

end Preadditive

end Mod

end CategoryTheory
