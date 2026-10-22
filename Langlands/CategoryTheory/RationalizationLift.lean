import Langlands.CategoryTheory.Rationalization
import Mathlib.CategoryTheory.Linear.LinearFunctor

open CategoryTheory
open scoped TensorProduct

noncomputable section

universe v₁ v₂ u₁ u₂

namespace Langlands.Rationalization

variable {C : Type u₁} [Category.{v₁} C] [Preadditive C]
  {D : Type u₂} [Category.{v₂} D] [Preadditive D] [Linear ℚ D]
  (F : C ⥤ D) [F.Additive]

/-- Extend the map on integral morphisms by rational scalar multiplication. -/
def liftHom {X Y : C} : Hom X Y →ₗ[ℚ] (F.obj X ⟶ F.obj Y) :=
  TensorProduct.AlgebraTensorModule.lift
    ((LinearMap.id : ℚ →ₗ[ℚ] ℚ).smulRight (F.mapLinearMap ℤ))

@[simp]
lemma liftHom_tmul {X Y : C} (q : ℚ) (f : X ⟶ Y) :
    liftHom F (q ⊗ₜ[ℤ] f) = q • F.map f := rfl

@[simp]
lemma liftHom_ofHom {X Y : C} (f : X ⟶ Y) :
    liftHom F (ofHom f) = F.map f := by
  simp

lemma liftHom_comp {X Y Z : C} (f : Hom X Y) (g : Hom Y Z) :
    liftHom F (comp X Y Z f g) = liftHom F f ≫ liftHom F g := by
  induction f using TensorProduct.inductionOn with
  | add f f' hf hf' => simp [hf, hf', Preadditive.add_comp]
  | tmul q f =>
    induction g using TensorProduct.inductionOn with
    | add g g' hg hg' => simp [hg, hg', Preadditive.comp_add]
    | tmul r g =>
      simp only [comp_tmul, liftHom_tmul, Functor.map_comp,
        Linear.smul_comp, Linear.comp_smul]
      rw [← mul_smul, mul_comm q r]

/-- The extension of an additive functor to the rationalized category. -/
def lift : Rationalization C ⥤ D where
  obj X := F.obj X.obj
  map := liftHom F
  map_id X := by
    change liftHom F ((1 : ℚ) ⊗ₜ[ℤ] 𝟙 X.obj) = 𝟙 (F.obj X.obj)
    simp
  map_comp := liftHom_comp F

instance : (lift F).Additive where
  map_add {_X _Y f g} := (liftHom F).map_add f g

@[simp]
lemma lift_map_tmul {X Y : C} (q : ℚ) (f : X ⟶ Y) :
    (lift F).map (q ⊗ₜ[ℤ] f : of X ⟶ of Y) = q • F.map f := rfl

/-- Restricting the extension along integral inclusion recovers the original functor. -/
def inclusionLiftIso : inclusion ⋙ lift F ≅ F :=
  NatIso.ofComponents (fun _ => Iso.refl _) (by
    intro X Y f
    change liftHom F (ofHom f) ≫ 𝟙 _ = 𝟙 _ ≫ F.map f
    simp)

/-- The induced algebra map on actual rational endomorphism rings. -/
def liftEnd (X : C) : End X →ₐ[ℚ] CategoryTheory.End (F.obj X) where
  toFun := liftHom F
  map_zero' := map_zero (liftHom F)
  map_one' := (lift F).map_id (of X)
  map_add' := map_add (liftHom F)
  map_mul' f g := liftHom_comp F g f
  commutes' q := by
    rw [algebraMap_eq, liftHom_tmul, F.map_id]
    rfl

@[simp]
lemma liftEnd_ofEnd (X : C) (f : CategoryTheory.End X) :
    liftEnd F X (ofEnd X f) = F.map f := by
  change liftHom F (ofHom f) = _
  simp

@[simp]
lemma liftEnd_endTensor (X : C) (q : ℚ) (f : CategoryTheory.End X) :
    liftEnd F X (endTensor X q f) = q • F.map f := rfl

end Langlands.Rationalization
