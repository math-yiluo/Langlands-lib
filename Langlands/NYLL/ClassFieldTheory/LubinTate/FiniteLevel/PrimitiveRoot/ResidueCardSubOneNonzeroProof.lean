/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)

Modified by Worker 233, 2026-11-16: extract only the proof of M341.008
(lines 123–145) from upstream commit
fbd320cd8b1b06487c58227e92eb135794267709; qualify the namespace with
Langlands.NYLL, use the fully applied published Statement as the theorem
type and unfold it, replace the imports by the target module and the
finite-field API, and replace the module documentation. The proof body
otherwise follows the source. See the paired Markdown and licenses/NYLL/.
-/

import Langlands.NYLL.ClassFieldTheory.LubinTate.FiniteLevel.PrimitiveRoot.DerivativeCardinalityStatements
import Mathlib.FieldTheory.Finite.Basic

/-!
# Nonvanishing of the residue cardinality minus one

The finite residue field sends its cardinality to zero, so the predecessor
of that cardinality maps to `-1`. The residue map therefore prevents its
cast in the base field from being zero.
-/

noncomputable section

universe u v

namespace Langlands.NYLL.LubinTate

open LocalFieldTheory.DiscreteValuationField

variable {K : Type u} [Field K]

/-- The natural number `q - 1` is nonzero in the local field. -/
theorem residueFieldNatCard_sub_one_cast_ne_zero
    (F : LocalField.{u, v} K) :
    residueFieldNatCard_sub_one_cast_ne_zeroStatement F := by
  unfold residueFieldNatCard_sub_one_cast_ne_zeroStatement
  have hcard :
      (Nat.card F.residueField : F.residueField) = 0 := by
    let := Fintype.ofFinite F.residueField
    rw [Nat.card_eq_fintype_card, Nat.cast_card_eq_zero]
  have hres :
      ((Nat.card F.residueField - 1 : ℕ) : F.residueField) ≠ 0 := by
    rw [Nat.cast_sub
      (Nat.le_of_lt
        (Finite.one_lt_card : 1 < Nat.card F.residueField)), hcard,
      Nat.cast_one, zero_sub]
    exact neg_ne_zero.mpr one_ne_zero
  intro hfield
  have hvaluation :
      ((Nat.card F.residueField - 1 : ℕ) : F.valuationSubring) = 0 := by
    apply Subtype.ext
    simpa using hfield
  have hreszero :
      ((Nat.card F.residueField - 1 : ℕ) : F.residueField) = 0 := by
    simpa using congrArg F.residueMap hvaluation
  exact hres hreszero

end Langlands.NYLL.LubinTate
