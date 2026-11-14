/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)

Modified by Worker 205, 2026-11-13: extract the indicated M266 source unit
from commit fbd320cd8b1b06487c58227e92eb135794267709, add the namespace
prefix, and use focused adapted imports. The statement is closed under
its original telescope; the proof uses that named proposition target.
Modified by Worker 563, 2026-11-14: reuse Worker 205's shared draft
revision 1 for Task 6176; retain the exact published target and the source
cardinality calculation, with the published M266.020 equivalence.
The retained license and notices are in licenses/NYLL/.
-/

import Langlands.NYLL.ClassFieldTheory.LocalClassFieldTheory.Finite.Existence.UnramifiedNormSubgroup.U024.Statements
import Langlands.NYLL.ClassFieldTheory.LocalClassFieldTheory.Finite.Existence.UnramifiedNormSubgroup.U020.Definitions
import Mathlib.SetTheory.Cardinal.Finite

/-! # Cardinality of the unramified norm quotient for nonzero degree -/

universe u

namespace Langlands.NYLL.LocalClassFieldTheory

theorem unramifiedNormQuotient_card_eq_degree :
    unramifiedNormQuotient_card_eq_degreeStatement.{u} := by
  intro K _ _ _ _ n _
  calc
    Nat.card (Kˣ ⧸ unramifiedNormSubgroup K n) =
        Nat.card (Multiplicative (ZMod n)) :=
      Nat.card_congr (unramifiedNormQuotientEquivZMod K n).toEquiv
    _ = Nat.card (ZMod n) := Nat.card_congr Multiplicative.toAdd
    _ = n := Nat.card_zmod n

end Langlands.NYLL.LocalClassFieldTheory
