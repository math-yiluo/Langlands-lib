/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import Mathlib.CategoryTheory.ObjectProperty.Kernels
public import Mathlib.CategoryTheory.Limits.Preserves.Shapes.Kernels

/-!
# Closure under kernels of an inverse image

If `P` is a property of objects of `C` closed under kernels (resp. cokernels), and `F : D ⥤ C`
preserves kernels (resp. cokernels), then `P.inverseImage F` is closed under kernels
(resp. cokernels).
-/

@[expose] public section

namespace CategoryTheory.ObjectProperty

open Limits

variable {C D : Type*} [Category* C] [Category* D] [HasZeroMorphisms C] [HasZeroMorphisms D]
  (P : ObjectProperty C) (F : D ⥤ C) [F.PreservesZeroMorphisms]

instance IsClosedUnderKernels.inverseImage [P.IsClosedUnderKernels]
    [PreservesLimitsOfShape WalkingParallelPair F] :
    (P.inverseImage F).IsClosedUnderKernels where
  kernels_le := by
    rintro _ ⟨f, k, hk, hf⟩
    exact P.prop_of_isLimit_kernelFork
      (KernelFork.isLimitMapConeEquiv k F (isLimitOfPreserves F hk)) hf.1 hf.2

instance IsClosedUnderCokernels.inverseImage [P.IsClosedUnderCokernels]
    [PreservesColimitsOfShape WalkingParallelPair F] :
    (P.inverseImage F).IsClosedUnderCokernels where
  cokernels_le := by
    rintro _ ⟨f, k, hk, hf⟩
    exact P.prop_of_isColimit_cokernelCofork
      (CokernelCofork.isColimitMapCoconeEquiv k F (isColimitOfPreserves F hk)) hf.1 hf.2

end CategoryTheory.ObjectProperty
