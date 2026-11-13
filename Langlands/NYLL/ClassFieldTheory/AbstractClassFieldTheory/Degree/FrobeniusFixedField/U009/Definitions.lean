/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import Langlands.NYLL.ClassFieldTheory.AbstractClassFieldTheory.Degree.Fields.Definitions

/-!
# Multiplicative profinite reduction

Modified by Worker 193: extract M014.009 from the pinned NYLL source,
prefix its namespace with Langlands.NYLL, and narrow the
imports to the dependencies of this definition. Retain the source body and
parameter telescope. See the paired Markdown and licenses/NYLL/LICENSE and NOTICE.
-/

namespace Langlands.NYLL.ClassFormation

noncomputable section

/-- Reduction modulo `n`, in the multiplicative presentation. -/
def zHatReductionMul (n : ℕ) (hn : 0 < n) :
    ZHatMul →ₜ* Multiplicative (ZMod n) where
  toFun z := Multiplicative.ofAdd (zHatReduction n hn z.toAdd)
  map_one' := by
    apply Multiplicative.ext
    exact map_zero (zHatReduction n hn)
  map_mul' x y := by
    apply Multiplicative.ext
    exact map_add (zHatReduction n hn) x.toAdd y.toAdd
  continuous_toFun := map_continuous (zHatReduction n hn)

end
end Langlands.NYLL.ClassFormation
