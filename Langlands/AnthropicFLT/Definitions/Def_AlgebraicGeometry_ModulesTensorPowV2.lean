/-
Ported from `Definitions/Def_AlgebraicGeometry_ModulesTensorPowV2.lean` of the Anthropic Lean formalization of Fermat's Last Theorem
(commit 6e837e75355538c7f80bab5b956861e86c4eacc2), Copyright 2026 Anthropic, PBC, licensed under the Apache
License, Version 2.0; see `licenses/Anthropic-FLT/LICENSE`, `NOTICE` and `ATTRIBUTION.md`.
The paired Markdown file lists the changes made by the port.
-/
import Langlands.MathlibBase
import Langlands.AnthropicFLT.Definitions.Def_SheafOfModules_MonoidalV2
set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false


set_option autoImplicit false

noncomputable section

universe u

open CategoryTheory MonoidalCategory

namespace AlgebraicGeometry.Scheme.Modules

variable {X : Scheme.{u}}

def tensorPowFLT (L : X.Modules) : ℕ → X.Modules
  | 0 => 𝟙_ X.Modules
  | n + 1 => tensorPowFLT L n ⊗ L

@[simp] theorem tensorPowFLT_zero (L : X.Modules) : L.tensorPowFLT 0 = 𝟙_ X.Modules := rfl

@[simp] theorem tensorPowFLT_succ (L : X.Modules) (n : ℕ) : L.tensorPowFLT (n + 1) = L.tensorPowFLT n ⊗ L := rfl

def tensorPowOneIso (L : X.Modules) : L.tensorPowFLT 1 ≅ L := λ_ L

end AlgebraicGeometry.Scheme.Modules

end
