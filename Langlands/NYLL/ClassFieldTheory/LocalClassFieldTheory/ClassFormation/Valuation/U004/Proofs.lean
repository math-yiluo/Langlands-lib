/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

/-
Modified by Worker 120, 14 November 2026: extract the proof of M140.004 from
Nyll/ClassFieldTheory/LocalClassFieldTheory/ClassFormation/Valuation.lean,
lines 62-76, at commit fbd320cd8b1b06487c58227e92eb135794267709. Prefix the
namespace with Langlands.NYLL, import only the published IntegerStatements
module, and prove the published target applied to all its parameters with the
original proof. Omit the theorem-only simp attribute, the source noncomputable
section and all other source declarations. See the paired Markdown; the
original LICENSE and NOTICE are retained in licenses/NYLL/.
-/

import Langlands.NYLL.ClassFieldTheory.LocalClassFieldTheory.ClassFormation.Valuation.IntegerStatements

/-!
# The Galois action on integer units

The integral-closure Galois action on `𝒪[L]ˣ` is given by the induced ring
automorphism of `𝒪[L]`, applied to units.
-/

namespace Langlands.NYLL.LocalClassFieldTheory

open Langlands.NYLL.LocalFieldTheory

universe u

open scoped ValuativeRel

/-- The integer-unit Galois action applies the restricted ring automorphism. -/
theorem galoisGroupIntegerUnitsMulDistribMulActionOfIsIntegralClosure_smul
    (K L : Type u) [Field K] [ValuativeRel K] [Field L] [ValuativeRel L]
    [Algebra K L]
    [Valuation.HasExtension (ValuativeRel.valuation K) (ValuativeRel.valuation L)]
    [IsIntegralClosure 𝒪[L] 𝒪[K] L]
    (σ : Gal(L/K)) (x : 𝒪[L]ˣ) :
    galoisGroupIntegerUnitsMulDistribMulActionOfIsIntegralClosure_smulStatement K L σ x := by
  unfold galoisGroupIntegerUnitsMulDistribMulActionOfIsIntegralClosure_smulStatement
  intro hIntegerAction
  apply Units.ext
  rfl

end Langlands.NYLL.LocalClassFieldTheory
