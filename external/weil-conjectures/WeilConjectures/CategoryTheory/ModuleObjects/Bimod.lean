/-
Copyright (c) 2026 Nailin Guan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Nailin Guan
-/
module

public import Mathlib.CategoryTheory.Monoidal.Bimod
public import Mathlib.CategoryTheory.Monoidal.Braided.Basic
public import WeilConjectures.Mathlib.CategoryTheory.Monoidal.Mod

/-!

# Module objects over a commutative ring object as bimodules

Let `C` be a braided monoidal category and `R : C` a commutative algebra object. Every left
`R`-module object `M` has a canonical right action `M ⊗ R ⟶ R ⊗ M ⟶ M` (first the braiding,
then the left action), which makes `M` an `R`-`R`-bimodule. We call bimodules of this form
*symmetric*. This identifies `Mod C R` with the full subcategory of symmetric bimodules in
`Bimod R R`:

* `Mod.toBimod : Mod C R ⥤ Bimod R R` is fully faithful;
* `Mod.fromBimod : Bimod R R ⥤ Mod C R` forgets the right action, and
  `Mod.toBimodFromBimodIso` identifies `toBimod (fromBimod P)` with `P` when `P` is symmetric.

Moreover, the tensor product (over `R`) of two symmetric bimodules is symmetric
(`Bimod.IsSymmetric.tensorBimod`). This is used to construct the relative tensor product
`M ⊗_R N` of module objects, see `WeilConjectures.CategoryTheory.ModuleObjects.Monoidal`.

-/

@[expose] public section

universe v u

open CategoryTheory MonoidalCategory BraidedCategory MonObj Limits

namespace CategoryTheory

variable {C : Type u} [Category.{v} C] [MonoidalCategory C] [BraidedCategory C]
  {R : C} [MonObj R] [IsCommMonObj R]

namespace Mod

@[reassoc]
lemma braiding_whiskerRight_smul (M : Mod C R) :
    (β_ R R).hom ▷ M.X ≫ (α_ R R M.X).hom ≫ R ◁ γ[R,M.X] ≫ γ[R,M.X] =
      (α_ R R M.X).hom ≫ R ◁ γ[R,M.X] ≫ γ[R,M.X] := by
  rw [← mul_act, ← comp_whiskerRight_assoc, IsCommMonObj.mul_comm, mul_act]

variable (R) in
/-- A left module object over a commutative algebra object, regarded as a bimodule: the right
action is the braiding followed by the left action. -/
@[simps]
def toBimodObj (M : Mod C R) : Bimod (Mon.mk R) (Mon.mk R) where
  X := M.X
  actLeft := γ[R,M.X]
  one_actLeft := one_act M.X
  left_assoc := mul_act M.X
  actRight := (β_ M.X R).hom ≫ γ[R,M.X]
  actRight_one := by
    change M.X ◁ η[R] ≫ (β_ M.X R).hom ≫ γ[R,M.X] = (ρ_ M.X).hom
    rw [braiding_naturality_right_assoc, one_act, braiding_leftUnitor]
  right_assoc := by
    change M.X ◁ μ[R] ≫ (β_ M.X R).hom ≫ γ[R,M.X] =
      (α_ M.X R R).inv ≫ ((β_ M.X R).hom ≫ γ[R,M.X]) ▷ R ≫ (β_ M.X R).hom ≫ γ[R,M.X]
    rw [braiding_naturality_right_assoc, mul_act, comp_whiskerRight, Category.assoc,
      braiding_naturality_left_assoc, braiding_tensor_right_hom, braiding_tensor_left_hom]
    simp only [Category.assoc, Iso.inv_hom_id_assoc, braiding_whiskerRight_smul]
  middle_assoc := by
    change γ[R,M.X] ▷ R ≫ (β_ M.X R).hom ≫ γ[R,M.X] =
      (α_ R M.X R).hom ≫ R ◁ ((β_ M.X R).hom ≫ γ[R,M.X]) ≫ γ[R,M.X]
    rw [braiding_naturality_left_assoc]
    erw [braiding_tensor_left_hom]
    simp only [Category.assoc, braiding_whiskerRight_smul, Iso.inv_hom_id_assoc,
      whiskerLeft_comp]

variable (R) in
/-- Left module objects over a commutative algebra object, regarded as bimodules. -/
@[simps]
def toBimod : Mod C R ⥤ Bimod (Mon.mk R) (Mon.mk R) where
  obj := toBimodObj R
  map f :=
    { hom := f.hom
      left_act_hom := act_hom f
      right_act_hom := by
        change ((β_ _ R).hom ≫ γ[R,_]) ≫ f.hom = f.hom ▷ R ≫ (β_ _ R).hom ≫ γ[R,_]
        rw [Category.assoc, act_hom, braiding_naturality_left_assoc] }

instance : (toBimod R : Mod C R ⥤ _).Faithful where
  map_injective h := hom_ext _ _ (congrArg Bimod.Hom.hom h)

/-- `toBimod` is fully faithful. -/
def fullyFaithfulToBimod : (toBimod R : Mod C R ⥤ _).FullyFaithful where
  preimage f := Hom.mk' f.hom f.left_act_hom

instance : (toBimod R : Mod C R ⥤ _).Full := fullyFaithfulToBimod.full

variable (R) in
/-- The left module object underlying a bimodule object. -/
@[simps]
def fromBimod : Bimod (Mon.mk R) (Mon.mk R) ⥤ Mod C R where
  obj P :=
    letI : ModObj R P.X :=
      { smul := P.actLeft
        one_smul := P.one_actLeft
        mul_smul := P.left_assoc }
    ⟨P.X⟩
  map f := Hom.mk' f.hom f.left_act_hom

omit [BraidedCategory C] [IsCommMonObj R] in
@[simp]
lemma fromBimod_obj_smul (P : Bimod (Mon.mk R) (Mon.mk R)) :
    γ[R,((fromBimod R).obj P).X] = P.actLeft :=
  rfl

/-- Forgetting the right action of the bimodule associated with a module object gives back the
module object. -/
def fromBimodToBimodIso : toBimod R ⋙ fromBimod R ≅ 𝟭 (Mod C R) :=
  NatIso.ofComponents (fun M ↦ isoMk (Iso.refl M.X) (by
    erw [Category.comp_id, whiskerLeft_id, Category.id_comp])) (fun f ↦ by
      ext
      exact (Category.comp_id f.hom).trans (Category.id_comp f.hom).symm)

end Mod

end CategoryTheory

namespace Bimod

open CategoryTheory

variable {C : Type u} [Category.{v} C] [MonoidalCategory C] [BraidedCategory C]

section

variable {A : Mon C}

/-- A bimodule over a commutative algebra object is *symmetric* if its right action is the
braiding followed by its left action. -/
def IsSymmetric (P : Bimod A A) : Prop :=
  P.actRight = (β_ P.X A.X).hom ≫ P.actLeft

lemma isSymmetric_regular [IsCommMonObj A.X] : (regular A).IsSymmetric :=
  (IsCommMonObj.mul_comm A.X).symm

variable [HasCoequalizers C] [∀ X : C, PreservesColimitsOfSize.{0, 0} (tensorLeft X)]
  [∀ X : C, PreservesColimitsOfSize.{0, 0} (tensorRight X)]

/-- The tensor product over a commutative algebra object of two symmetric bimodules is
symmetric. -/
lemma IsSymmetric.tensorBimod {P Q : Bimod A A} (hP : P.IsSymmetric) (hQ : Q.IsSymmetric) :
    (P.tensorBimod Q).IsSymmetric := by
  change TensorBimod.actRight P Q = (β_ (TensorBimod.X P Q) A.X).hom ≫ TensorBimod.actLeft P Q
  refine (cancel_epi ((tensorRight _).map (coequalizer.π _ _))).1 ?_
  dsimp [TensorBimod.X]
  rw [TensorBimod.π_tensor_id_actRight, braiding_naturality_left_assoc,
    TensorBimod.whiskerLeft_π_actLeft, hQ]
  have hP' : P.actLeft = (β_ P.X A.X).inv ≫ P.actRight := by rw [hP, Iso.inv_hom_id_assoc]
  rw [hP', comp_whiskerRight, Category.assoc, coequalizer.condition, braiding_tensor_left_hom]
  simp

end

variable {R : C} [MonObj R] [IsCommMonObj R]

lemma isSymmetric_toBimodObj (M : Mod C R) : (Mod.toBimodObj R M).IsSymmetric := rfl

/-- A symmetric bimodule is isomorphic to the bimodule associated with its underlying module
object. -/
@[simps!]
def IsSymmetric.iso {P : Bimod (Mon.mk R) (Mon.mk R)} (h : P.IsSymmetric) :
    Mod.toBimodObj R ((Mod.fromBimod R).obj P) ≅ P :=
  isoOfIso (Iso.refl P.X) (by
      erw [Category.comp_id, whiskerLeft_id, Category.id_comp]
      rfl) (by
    change ((β_ P.X R).hom ≫ P.actLeft) ≫ 𝟙 _ = 𝟙 _ ▷ R ≫ P.actRight
    rw [h]
    simp)

end Bimod
