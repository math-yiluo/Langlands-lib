/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

/-
Modified by Worker 231 on 2026-11-13: extracted the source units recorded
in the paired Markdown; prefixed the namespace with Langlands.NYLL and
reduced imports. Source data bodies and parameter binding are preserved.
The original LICENSE and NOTICE are retained in licenses/NYLL/.
-/

import Mathlib.FieldTheory.Galois.NormalBasis
import Mathlib.NumberTheory.LocalField.Basic

namespace Langlands.NYLL.CyclicCohomology

noncomputable section

universe u

open scoped ValuativeRel
open Filter

variable (K L : Type u) [Field K] [Field L] [Algebra K L]
  [FiniteDimensional K L] [IsGalois K L]

variable [ValuativeRel K]

/-- Multiplication by a base integer-ring element, as an `𝒪_K`-linear endomorphism
of the extension field. -/
def baseIntegerScalarMulLinearMap (a : 𝒪[K]) : L →ₗ[𝒪[K]] L where
  toFun x := algebraMap 𝒪[K] L a * x
  map_add' := by
    intro x y
    rw [mul_add]
  map_smul' := by
    intro r x
    simp [Algebra.smul_def, mul_comm, mul_left_comm]


/-- The image of an `𝒪_K`-submodule under multiplication by a base
integer-ring element. -/
def baseIntegerScalarMulSubmodule (a : 𝒪[K]) (N : Submodule 𝒪[K] L) :
    Submodule 𝒪[K] L :=
  N.map (baseIntegerScalarMulLinearMap K L a)


end
end Langlands.NYLL.CyclicCohomology
