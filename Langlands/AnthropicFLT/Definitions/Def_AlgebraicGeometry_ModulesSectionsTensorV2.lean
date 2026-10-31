/-
Ported from `Definitions/Def_AlgebraicGeometry_ModulesSectionsTensorV2.lean` of the Anthropic Lean formalization of Fermat's Last Theorem
(commit 6e837e75355538c7f80bab5b956861e86c4eacc2), Copyright 2026 Anthropic, PBC, licensed under the Apache
License, Version 2.0; see `licenses/Anthropic-FLT/LICENSE`, `NOTICE` and `ATTRIBUTION.md`.
The paired Markdown file lists the changes made by the port.
-/
import Mathlib
import Langlands.AnthropicFLT.Definitions.Def_PresheafOfModules_InternalHom
import Langlands.AnthropicFLT.Definitions.Def_SheafOfModules_MonoidalV2
import Langlands.AnthropicFLT.Definitions.Def_AlgebraicGeometry_ModulesTensorPowV2
import Langlands.AnthropicFLT.Definitions.Def_AlgebraicGeometry_ModulesSectionsTensor
set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false


set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

universe u

open CategoryTheory MonoidalCategory Opposite TensorProduct

noncomputable section

namespace AlgebraicGeometry.Scheme.Modules

variable {X : Scheme.{u}}

section Hom

variable (L M : X.Modules)

end Hom

section Sections

variable {L M : X.Modules} {U : X.Opens}

end Sections

section Pow

variable {L : X.Modules} {U : X.Opens}

end Pow

section Frame

variable {M : X.Modules} {U : X.Opens}

namespace IsFrameOn

variable {s : Γ(M, U)} {V : X.Opens}

end IsFrameOn

end Frame

end AlgebraicGeometry.Scheme.Modules

end
