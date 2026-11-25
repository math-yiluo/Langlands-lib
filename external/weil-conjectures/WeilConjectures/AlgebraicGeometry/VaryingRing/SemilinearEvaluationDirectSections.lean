/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.VaryingRing.VaryingRingOperations

/-! # Native section normalization for semilinear direct-image evaluation

Source: Zheng, Construction 4.1
(blueprint: lem-sf-scalar-evaluation-direct-sections). -/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 4096
set_option backward.isDefEq.respectTransparency true
set_option backward.isDefEq.respectTransparency.types true

universe u
open CategoryTheory Opposite

namespace AlgebraicGeometry.ProEtale.VaryingRing

variable (R : ℕ → CommRingCat.{u + 1}) (φ : ∀ n : ℕ, R (n + 1) ⟶ R n)

/-- Direct-image evaluation retains sections in the native evaluation carrier.
Source: Zheng, Construction 4.1 (blueprint: lem-sf-scalar-evaluation-direct-sections).
Proof: the existing unique comparison is normalized on the common fibre-product
section carrier. Unfold its choice and apply that normalization to the same section;
equality on this carrier implies heterogeneous equality in the native carrier. -/
theorem moduleEvalP_sections_heq {X Y : Scheme.{u}} (f : X ⟶ Y)
    (M : Modules R φ X) (n : ℕ) (H : Y.ProEtᵒᵖ)
    (x : ((eval R φ Y n).obj ((push R φ f).obj M)).val.obj H) :
    HEq (((moduleEvalP R φ f n).hom.app M).val.app H x) x := by
  apply heq_of_eq
  exact (moduleEvalP_existsUnique R φ f n).choose_spec.1 M H.unop x

end AlgebraicGeometry.ProEtale.VaryingRing
