/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.FourierTransform.FdPullbackAugmentationCounitMatching
public import WeilConjectures.FourierTransform.PullbackCommonStrictTowerModels

/-! # Uniqueness of the normalized integral pullback comparison

Source: trace-definition whole-tower comparison, steps 8--10; Stacks 0941 and 099N.
(blueprint: lem-fd-pullback-roos-matching-uniqueness). -/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 4096
set_option genSizeOf false
set_option genSizeOfSpec false
set_option genInjectivity false

universe u w
open CategoryTheory CategoryTheory.Limits Opposite AlgebraicGeometry
open AlgebraicGeometry.Scheme
namespace WeilConjectures

variable (l : ℕ) [Fact l.Prime]
  (Ω : Type w) [Field Ω] [Algebra ℚ_[l] Ω] [IsAlgClosure ℚ_[l] Ω]

end WeilConjectures
