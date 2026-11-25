/-
Copyright (c) 2026 Christian Merten. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Merten
-/
module

public import Mathlib.CategoryTheory.Linear.FunctorCategory
public import Mathlib.CategoryTheory.Limits.Preserves.Shapes.Kernels
public import Mathlib.CategoryTheory.Sites.Abelian
public import WeilConjectures.Mathlib.CategoryTheory.Linear.LinearFunctor

/-!
# Linearity of sheafification

For an `R`-linear preadditive category `D`, the category `Sheaf J D` is `R`-linear (this
holds by instances, as sheaves form a full subcategory of presheaves), and the
sheafification functor `presheafToSheaf J D` is `R`-linear, being the left adjoint of the
(componentwise, hence `R`-linear) inclusion `sheafToPresheaf J D`. This is the `R`-linear
analogue of `CategoryTheory.presheafToSheaf_additive`.

Kernels in the abelian category `Sheaf J D` are computed sectionwise
(`CategoryTheory.Sheaf.kernelObjIso`).
-/

@[expose] public section

universe w' w v u

namespace CategoryTheory

variable {C : Type u} [Category.{v} C] (R : Type*) [Semiring R]
  {D : Type w} [Category.{w'} D] [Preadditive D] [Linear R D]
  {J : GrothendieckTopology C} [HasSheafify J D]

example : Linear R (Sheaf J D) := inferInstance

example : (sheafToPresheaf J D).Linear R := inferInstance

instance presheafToSheaf_linear : (presheafToSheaf J D).Linear R :=
  (sheafificationAdjunction J D).left_adjoint_linear

/-- The constant sheaf functor is `R`-linear, being the composite of the constant presheaf
functor and of the sheafification functor. -/
instance constantSheaf_linear : (constantSheaf J D).Linear R where
  map_smul {X Y} f r := by
    change (presheafToSheaf J D).map ((Functor.const _).map (r • f)) =
      r • (presheafToSheaf J D).map ((Functor.const _).map f)
    rw [← Functor.map_smul]
    rfl

section Kernel

open Limits

variable {C : Type u} [Category.{v} C] {J : GrothendieckTopology C}
  {D : Type w} [Category.{w'} D] [Abelian D] [HasSheafify J D]

/-- The kernel of a morphism `φ : F ⟶ G` in the abelian category of `D`-valued sheaves
(`CategoryTheory.sheafIsAbelian`) is computed sectionwise: its sections over `U` are the
kernel of `φ` on sections over `U`, since the inclusion of sheaves into presheaves and the
evaluations preserve limits. (blueprint: `def-pur-abelian-sheaf-kernel`) -/
noncomputable def Sheaf.kernelObjIso {F G : Sheaf J D} (φ : F ⟶ G) (U : Cᵒᵖ) :
    (kernel φ).obj.obj U ≅ kernel (φ.hom.app U) :=
  PreservesKernel.iso (sheafToPresheaf J D ⋙ (evaluation Cᵒᵖ D).obj U) φ

/-- Under `CategoryTheory.Sheaf.kernelObjIso`, the inclusion of the kernel is sectionwise the
inclusion of the kernel. -/
@[reassoc (attr := simp)]
lemma Sheaf.kernelObjIso_hom_comp_ι {F G : Sheaf J D} (φ : F ⟶ G) (U : Cᵒᵖ) :
    (Sheaf.kernelObjIso φ U).hom ≫ kernel.ι (φ.hom.app U) = (kernel.ι φ).hom.app U := by
  rw [Sheaf.kernelObjIso, PreservesKernel.iso_hom]
  exact kernelComparison_comp_ι _ _

end Kernel

end CategoryTheory
