/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import Mathlib.CategoryTheory.Abelian.Basic
public import Mathlib.CategoryTheory.Limits.Preserves.Shapes.Kernels
public import Mathlib.CategoryTheory.ObjectProperty.Kernels

/-!
# The essential image of a full exact functor is closed under kernels and cokernels

Let `F : C ⥤ D` be a full additive functor between abelian categories. If `F` preserves finite
limits, its essential image is closed under kernels; if it preserves finite colimits, it is
closed under cokernels. Indeed a morphism between objects of the essential image is, up to
isomorphism, `F.map g`, whose kernel is `F.obj (kernel g)`.
-/

@[expose] public section

namespace CategoryTheory

open Limits

variable {C D : Type*} [Category* C] [Category* D] [Abelian C] [Abelian D] (F : C ⥤ D) [F.Full]
  [F.Additive]

/-- The essential image of a full additive functor preserving finite limits between abelian
categories is closed under kernels. -/
instance Functor.essImage_isClosedUnderKernels [PreservesFiniteLimits F] :
    F.essImage.IsClosedUnderKernels where
  kernels_le := by
    rintro _ ⟨f, k, hk, ⟨A₁, ⟨e₁⟩⟩, ⟨A₂, ⟨e₂⟩⟩⟩
    obtain ⟨g, hg⟩ := F.map_surjective (e₁.hom ≫ f ≫ e₂.inv)
    exact ⟨Limits.kernel g, ⟨PreservesKernel.iso F g ≪≫
      kernel.mapIso (F.map g) f e₁ e₂ (by simp [hg]) ≪≫
      (hk.conePointUniqueUpToIso (kernelIsKernel f)).symm⟩⟩

/-- The essential image of a full additive functor preserving finite colimits between abelian
categories is closed under cokernels. -/
instance Functor.essImage_isClosedUnderCokernels [PreservesFiniteColimits F] :
    F.essImage.IsClosedUnderCokernels where
  cokernels_le := by
    rintro _ ⟨f, k, hk, ⟨A₁, ⟨e₁⟩⟩, ⟨A₂, ⟨e₂⟩⟩⟩
    obtain ⟨g, hg⟩ := F.map_surjective (e₁.hom ≫ f ≫ e₂.inv)
    exact ⟨Limits.cokernel g, ⟨PreservesCokernel.iso F g ≪≫
      cokernel.mapIso (F.map g) f e₁ e₂ (by simp [hg]) ≪≫
      (hk.coconePointUniqueUpToIso (cokernelIsCokernel f)).symm⟩⟩

end CategoryTheory
