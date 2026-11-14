/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

/-
Modifications by Worker 135, 14 November 2026:
Extract the proof of M129.020 (lines 179–191) from
Nyll/ValuedFieldTheory/LocalField/NonarchimedeanLocalField/Norm.lean at
fbd320cd8b1b06487c58227e92eb135794267709. Prefix the namespace with
Langlands.NYLL and prove the published closed statement by introducing its
complete telescope before the unchanged source tactic proof. Import only the
target statement module. Omit all other source declarations. See paired
Markdown. The upstream LICENSE and NOTICE are preserved in licenses/NYLL/.
-/

import Langlands.NYLL.ValuedFieldTheory.LocalField.NonarchimedeanLocalField.Norm.InverseStatements

/-!
# The norm value of a valuation-ring unit times that of its inverse

The exact proof of NYLL M129.020.
-/

namespace Langlands.NYLL.LocalFieldTheory.IsNonarchimedeanLocalField

open scoped ValuativeRel

/-- The norm value constructed from an integer unit multiplied by its inverse is one. -/
theorem normIntegerUnitsValue_mul_inv.{u, v} :
    normIntegerUnitsValue_mul_invStatement.{u, v} := by
  intro K L _ _ _ _ _ _ x
  ext
  change Algebra.norm K (((x : 𝒪[L]ˣ) : 𝒪[L]) : L) *
      Algebra.norm K (((x⁻¹ : 𝒪[L]ˣ) : 𝒪[L]) : L) = 1
  have hx : (((x : 𝒪[L]ˣ) : 𝒪[L]) : L) *
      (((x⁻¹ : 𝒪[L]ˣ) : 𝒪[L]) : L) = 1 := by
    exact congrArg (fun u : 𝒪[L]ˣ => ((u : 𝒪[L]) : L)) (mul_inv_cancel x)
  rw [← map_mul (Algebra.norm K), hx, map_one]

end Langlands.NYLL.LocalFieldTheory.IsNonarchimedeanLocalField
