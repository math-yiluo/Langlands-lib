/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)

Modified by Worker 485, 2026-11-14: extract the proof of M337.006 (lines
77–84) from upstream commit fbd320cd8b1b06487c58227e92eb135794267709;
prefix the namespace and opened namespace with Langlands.NYLL; import the
published Prop target and the M337.004 proof module and state the theorem as
that target; inline the proof term of the unported source lemma
existsUnique_mul_eq_of_isUnit (M337.005, lines 70–75), which is the Mathlib
expression recorded in the paired Markdown; replace the module documentation.
The retained license and notices are in licenses/NYLL/.
-/

import Langlands.NYLL.ClassFieldTheory.LubinTate.FormalModule.CoefficientEquation.U004.Proofs

/-!
# Unique solution of the scalar coefficient equation

Exact proof of NYLL M337.006 against its published target.
-/

universe u v

namespace Langlands.NYLL.LubinTate.SameUniformizer

open Langlands.NYLL.LocalFieldTheory.DiscreteValuationField

variable {K : Type u} [Field K]
variable {F : LocalField.{u, v} K} {π : F.valuationSubring}

/-- The scalar coefficient equation in positive total degree has a
unique solution in the valuation ring. -/
theorem existsUnique_one_sub_uniformizer_pow_mul_eq
    (hπ : F.toCompleteDVF.valuation.IsUniformizer (π : K))
    {r : ℕ} (hr : r ≠ 0) (b : F.valuationSubring) :
    existsUnique_one_sub_uniformizer_pow_mul_eqStatement hπ hr b :=
  (IsUnit.isUnit_iff_mulLeft_bijective.mp
    (isUnit_one_sub_uniformizer_pow hπ hr)).existsUnique b

end Langlands.NYLL.LubinTate.SameUniformizer
