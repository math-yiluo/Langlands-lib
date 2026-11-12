/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

/-
Modifications by Worker 120, 9 November 2026: extract only M128.016 from
Nyll/ValuedFieldTheory/LocalField/NonarchimedeanLocalField/Basic.lean
at fbd320cd8b1b06487c58227e92eb135794267709; add Langlands.NYLL to the
namespace. Preserve the original import, parameters and definition body.
LICENSE and NOTICE are in licenses/NYLL/.
-/

import Mathlib.NumberTheory.LocalField.Basic

/-! # Inclusion of valuation-integer units into field units -/

namespace Langlands.NYLL.LocalFieldTheory.IsNonarchimedeanLocalField

noncomputable section

universe u

open scoped ValuativeRel

/-- The canonical inclusion of valuation-integer units into field units. -/
def integerUnitsToFieldUnits (K : Type u) [Field K] [ValuativeRel K] : 𝒪[K]ˣ →* Kˣ :=
  Units.map (algebraMap 𝒪[K] K).toMonoidHom

end

end Langlands.NYLL.LocalFieldTheory.IsNonarchimedeanLocalField
