import Mathlib.CategoryTheory.Linear.Basic
import Mathlib.CategoryTheory.Preadditive.AdditiveFunctor
import Mathlib.LinearAlgebra.TensorProduct.Tower
import Mathlib.Algebra.Module.LinearMap.Rat
import Mathlib.Algebra.Algebra.Bilinear

/-! # Rationalization of a preadditive category -/

noncomputable section

open CategoryTheory
open scoped TensorProduct

universe v u

namespace Langlands

/-- The objects of the rationalization are precisely wrapped objects of `C`. -/
structure Rationalization (C : Type u) where
  of ::
  obj : C

namespace Rationalization

variable {C : Type u} [Category.{v} C] [Preadditive C]

/-- The rationalized group of morphisms. -/
abbrev Hom (X Y : C) := ℚ ⊗[ℤ] (X ⟶ Y)

/-- The explicit identification with the convention `Hom ⊗ ℚ`. -/
def homTensorComm (X Y : C) : Hom X Y ≃ₗ[ℤ] (X ⟶ Y) ⊗[ℤ] ℚ :=
  TensorProduct.comm ℤ ℚ (X ⟶ Y)

@[simp] theorem homTensorComm_tmul (X Y : C) (q : ℚ) (f : X ⟶ Y) :
    homTensorComm X Y (q ⊗ₜ[ℤ] f) = f ⊗ₜ[ℤ] q := rfl

/-- Composition obtained from the tensor universal property. -/
def comp (X Y Z : C) : Hom X Y →ₗ[ℤ] Hom Y Z →ₗ[ℤ] Hom X Z :=
  TensorProduct.map₂ (LinearMap.mul ℤ ℚ) (CategoryTheory.Linear.comp (S := ℤ) X Y Z)

@[simp] theorem comp_tmul {X Y Z : C} (q r : ℚ) (f : X ⟶ Y) (g : Y ⟶ Z) :
    comp X Y Z (q ⊗ₜ[ℤ] f) (r ⊗ₜ[ℤ] g) = (q * r) ⊗ₜ[ℤ] (f ≫ g) := rfl

/-- The rational identity. -/
def identity (X : C) : Hom X X := (1 : ℚ) ⊗ₜ[ℤ] 𝟙 X

@[simp] theorem identity_comp {X Y : C} (f : Hom X Y) :
    comp X X Y (identity X) f = f := by
  induction f using TensorProduct.inductionOn with
  | tmul q f => simp [identity]
  | add f g hf hg => simp [hf, hg]

@[simp] theorem comp_identity {X Y : C} (f : Hom X Y) :
    comp X Y Y f (identity Y) = f := by
  induction f using TensorProduct.inductionOn with
  | tmul q f => simp [identity]
  | add f g hf hg => simp [hf, hg]

theorem comp_assoc {W X Y Z : C} (f : Hom W X) (g : Hom X Y) (h : Hom Y Z) :
    comp W Y Z (comp W X Y f g) h = comp W X Z f (comp X Y Z g h) := by
  induction f using TensorProduct.inductionOn with
  | add f f' hf hf' => simp [hf, hf']
  | tmul q f =>
    induction g using TensorProduct.inductionOn with
    | add g g' hg hg' => simp [hg, hg']
    | tmul r g =>
      induction h using TensorProduct.inductionOn with
      | add h h' hh hh' => simp only [map_add, hh, hh']
      | tmul s h => simp [mul_assoc, Category.assoc]

instance : Category.{v} (Rationalization C) where
  Hom X Y := Hom X.obj Y.obj
  id X := identity X.obj
  comp f g := comp _ _ _ f g
  id_comp := identity_comp
  comp_id := comp_identity
  assoc := comp_assoc

instance : Preadditive (Rationalization C) where
  homGroup X Y := inferInstanceAs (AddCommGroup (Hom X.obj Y.obj))
  add_comp X Y Z f f' g := (comp X.obj Y.obj Z.obj).map_add₂ f f' g
  comp_add X Y Z f g g' := (comp X.obj Y.obj Z.obj f).map_add g g'

instance (X Y : Rationalization C) : Module ℚ (X ⟶ Y) :=
  inferInstanceAs (Module ℚ (Hom X.obj Y.obj))

instance : Linear ℚ (Rationalization C) where
  homModule X Y := inferInstanceAs (Module ℚ (Hom X.obj Y.obj))
  smul_comp X Y Z q f g := by
    change comp X.obj Y.obj Z.obj (q • f) g = q • comp X.obj Y.obj Z.obj f g
    exact map_rat_smul ((comp X.obj Y.obj Z.obj).flip g) q f
  comp_smul X Y Z f q g := map_rat_smul (comp X.obj Y.obj Z.obj f) q g

/-- Integral morphisms map to tensors with coefficient one. -/
def ofHom {X Y : C} : (X ⟶ Y) →ₗ[ℤ] Hom X Y :=
  TensorProduct.mk ℤ ℚ (X ⟶ Y) 1

@[simp] theorem ofHom_apply {X Y : C} (f : X ⟶ Y) :
    ofHom f = (1 : ℚ) ⊗ₜ[ℤ] f := rfl

/-- The canonical additive functor to the rationalization. -/
def inclusion : C ⥤ Rationalization C where
  obj := of
  map := ofHom
  map_id X := rfl
  map_comp f g := by
    change ofHom (f ≫ g) = comp _ _ _ (ofHom f) (ofHom g)
    simp

instance : (inclusion (C := C)).Additive where
  map_add {_X _Y f g} := map_add ofHom f g

/-- The actual endomorphism algebra of the rationalized category. -/
abbrev End (X : C) := CategoryTheory.End (of X)

/-- The canonical map of integral endomorphism rings. -/
def ofEnd (X : C) : CategoryTheory.End X →+* End X where
  toFun := ofHom
  map_zero' := map_zero ofHom
  map_one' := rfl
  map_add' := map_add ofHom
  map_mul' f g := by change ofHom (g ≫ f) = comp X X X (ofHom g) (ofHom f); simp

/-- The rational composition, bundled as a Q-bilinear map. -/
def compLinear (X Y Z : C) : Hom X Y →ₗ[ℚ] Hom Y Z →ₗ[ℚ] Hom X Z :=
  CategoryTheory.Linear.comp (S := ℚ) (of X) (of Y) (of Z)

@[simp] theorem compLinear_tmul {X Y Z : C} (q r : ℚ)
    (f : X ⟶ Y) (g : Y ⟶ Z) :
    compLinear X Y Z (q ⊗ₜ[ℤ] f) (r ⊗ₜ[ℤ] g) =
      (q * r) ⊗ₜ[ℤ] (f ≫ g) := rfl

@[simp] theorem ofEnd_apply (X : C) (f : CategoryTheory.End X) :
    ofEnd X f = (1 : ℚ) ⊗ₜ[ℤ] f := rfl

/-- A pure tensor viewed as a rational endomorphism. -/
def endTensor (X : C) (q : ℚ) (f : CategoryTheory.End X) : End X := q ⊗ₜ[ℤ] f

@[simp] theorem end_mul_tmul (X : C) (q r : ℚ) (f g : CategoryTheory.End X) :
    endTensor X q f * endTensor X r g = endTensor X (q * r) (f * g) := by
  change comp X X X (r ⊗ₜ[ℤ] g) (q ⊗ₜ[ℤ] f) = _
  simp [endTensor, mul_comm]

/-- The Q-algebra structure uses the tensor identity as its unit. -/
@[simp] theorem algebraMap_eq (X : C) (q : ℚ) :
    algebraMap ℚ (End X) q = q ⊗ₜ[ℤ] 𝟙 X := by
  change q • ((1 : ℚ) ⊗ₜ[ℤ] 𝟙 X) = _
  simp [TensorProduct.smul_tmul']

/-- Endomorphisms of the target act by postcomposition. -/
def postAction (X Y : C) : End Y →ₐ[ℚ] Module.End ℚ (Hom X Y) where
  toFun b := CategoryTheory.Linear.rightComp ℚ (of X) b
  map_zero' := by apply LinearMap.ext; intro f; simp [CategoryTheory.Linear.rightComp]
  map_one' := by apply LinearMap.ext; intro f; simp [CategoryTheory.Linear.rightComp]
  map_add' b b' := by
    apply LinearMap.ext
    intro f
    exact Preadditive.comp_add (of X) (of Y) (of Y) f b b'
  map_mul' b b' := by apply LinearMap.ext; intro f; simp [CategoryTheory.Linear.rightComp, Category.assoc]
  commutes' q := by
    apply LinearMap.ext
    intro f
    change f ≫ (q • 𝟙 (of Y)) = q • f
    rw [Linear.comp_smul, Category.comp_id]

/-- Precomposition by an endomorphism of the source. -/
def preAction (X Y : C) (a : End X) : Module.End ℚ (Hom X Y) :=
  CategoryTheory.Linear.leftComp ℚ (of Y) a

@[simp] theorem preAction_one (X Y : C) : preAction X Y 1 = 1 := by
  apply LinearMap.ext
  intro f
  exact identity_comp f

theorem preAction_mul (X Y : C) (a a' : End X) (f : Hom X Y) :
    preAction X Y (a * a') f = preAction X Y a' (preAction X Y a f) :=
  Category.assoc a' a f

theorem actions_commute (X Y : C) (a : End X) (b : End Y) (f : Hom X Y) :
    postAction X Y b (preAction X Y a f) = preAction X Y a (postAction X Y b f) :=
  Category.assoc a f b

@[simp] theorem postAction_ofEnd {X Y : C} (b : CategoryTheory.End Y) (f : X ⟶ Y) :
    postAction X Y (ofEnd Y b) (ofHom f) = ofHom (f ≫ b) := by
  change comp X Y Y (ofHom f) (ofHom b) = ofHom (f ≫ b)
  simp

@[simp] theorem preAction_ofEnd {X Y : C} (a : CategoryTheory.End X) (f : X ⟶ Y) :
    preAction X Y (ofEnd X a) (ofHom f) = ofHom (a ≫ f) := by
  change comp X X Y (ofHom a) (ofHom f) = ofHom (a ≫ f)
  simp

end Rationalization
end Langlands
