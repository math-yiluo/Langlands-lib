/-
Ported from `Definitions/Def_AlgebraicGeometry_OModulePresheafEulerChar.lean` of the Anthropic Lean formalization of
Fermat's Last Theorem (commit 6e837e75355538c7f80bab5b956861e86c4eacc2), Copyright 2026
Anthropic, PBC, licensed under the Apache License, Version 2.0; see
`licenses/Anthropic-FLT/LICENSE`, `NOTICE` and `ATTRIBUTION.md`.
Modified: FLT module names are prefixed by `Langlands.AnthropicFLT`; the FLT lakefile options
are set after the imports. The paired Markdown file lists
the changes.
-/
import Langlands.AnthropicFLT.Definitions.Def_AlgebraicGeometry_OrderedAffineCoverCech
import Mathlib.LinearAlgebra.Dimension.Finrank
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

noncomputable section

universe u

namespace AlgebraicGeometry.OModulePresheaf

open CategoryTheory

variable {R : Type u} [CommRing R] {V : Scheme.{u}} {π : V ⟶ Spec (.of R)}
variable (F : OModulePresheaf π) (K : V.OrderedAffineCover)

def cechFinrank : ℕ → ℕ
  | 0 => Module.finrank R (F.H0 K)
  | i + 1 => Module.finrank R (F.HSucc K i)

theorem cechFinrank_zero : F.cechFinrank K 0 = Module.finrank R (F.H0 K) := rfl

theorem cechFinrank_succ (i : ℕ) : F.cechFinrank K (i + 1) = Module.finrank R (F.HSucc K i) := rfl

def eulerChar : ℤ :=
  ∑ i ∈ Finset.range (Fintype.card K.ι), (-1 : ℤ) ^ i * (F.cechFinrank K i : ℤ)

theorem eulerChar_def :
    F.eulerChar K = ∑ i ∈ Finset.range (Fintype.card K.ι), (-1 : ℤ) ^ i * (F.cechFinrank K i : ℤ) := rfl

end AlgebraicGeometry.OModulePresheaf

end
