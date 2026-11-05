import Mathlib.CategoryTheory.Monoidal.Cartesian.Mod

/-! # Images of internal actions under monoidal functors -/

universe u₁ u₂ v₁ v₂

open CategoryTheory MonoidalCategory Functor.LaxMonoidal
open scoped CategoryTheory.MonObj CategoryTheory.Obj

namespace Langlands.MonoidalActionMap

section Monoidal

variable {C : Type u₁} [Category.{v₁} C] [MonoidalCategory C]
variable {D : Type u₂} [Category.{v₂} D] [MonoidalCategory D]
variable (F : C ⥤ D) [F.LaxMonoidal] (M X : C) [MonObj M] [ModObj M X]

/-- The image action uses the monoidal structure map followed by the image of
its actual action map. -/
abbrev mappedModObj : ModObj (F.obj M) (F.obj X) where
  smul := Functor.LaxMonoidal.μ F M X ≫ F.map γ[M, X]
  one_smul := by simp [← F.map_comp]
  mul_smul := by
    change (Functor.LaxMonoidal.μ F M M ≫ F.map μ[M]) ▷ F.obj X ≫
        (Functor.LaxMonoidal.μ F M X ≫ F.map γ[M, X]) =
      (α_ (F.obj M) (F.obj M) (F.obj X)).hom ≫
        F.obj M ◁ (Functor.LaxMonoidal.μ F M X ≫ F.map γ[M, X]) ≫
          (Functor.LaxMonoidal.μ F M X ≫ F.map γ[M, X])
    simp_rw [comp_whiskerRight, Category.assoc,
      μ_natural_left_assoc, MonoidalCategory.whiskerLeft_comp, Category.assoc,
      μ_natural_right_assoc]
    slice_lhs 3 4 => rw [← F.map_comp, ModObj.mul_smul_self]
    simp

end Monoidal

section Cartesian

open CartesianMonoidalCategory

variable {C : Type u₁} [Category.{v₁} C] [CartesianMonoidalCategory C]
variable {D : Type u₂} [Category.{v₂} D] [CartesianMonoidalCategory D]
variable (F : C ⥤ D) [F.Monoidal] (M X : C) [MonObj M] [ModObj M X]

attribute [local instance] mappedModObj

/-- The image shear is the image of the original shear, conjugated by the
canonical product comparison isomorphisms. -/
theorem mapped_leftSMul :
    ModObj.leftSMul (F.obj M) (F.obj X) =
      Functor.LaxMonoidal.μ F M X ≫ F.map (ModObj.leftSMul M X) ≫
        Functor.OplaxMonoidal.δ F X X := by
  apply CartesianMonoidalCategory.hom_ext
  · simp only [Category.assoc, Functor.OplaxMonoidal.δ_fst,
      ← F.map_comp, ModObj.leftSMul_fst]
    rfl
  · simp [← F.map_comp]

/-- A monoidal functor between Cartesian monoidal categories preserves
invertibility of the actual action shear. -/
theorem isIso_mapped_leftSMul [IsIso (ModObj.leftSMul M X)] :
    IsIso (ModObj.leftSMul (F.obj M) (F.obj X)) := by
  rw [mapped_leftSMul F M X]
  infer_instance

end Cartesian

end Langlands.MonoidalActionMap
