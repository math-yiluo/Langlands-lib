/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import Langlands.NYLL.ClassFieldTheory.AbstractClassFieldTheory.Degree.Fields.Definitions
import Langlands.NYLL.GaloisCohomology.ProfiniteIntegers.ProfiniteInteger.U002.Definitions

/-!
# Natural profinite power map

Modified by Worker 193: extract M014.006 from the pinned NYLL source,
prefix its namespace with Langlands.NYLL, and narrow the
imports to the dependencies of this definition. Retain the source body and
parameter telescope. See the paired Markdown and licenses/NYLL/LICENSE and NOTICE.
-/

namespace Langlands.NYLL.ClassFormation

noncomputable section

/-- Multiplication by `n` on `ℤ̂`, in the multiplicative presentation. -/
def zHatPowNat (n : ℕ) : ZHatMul →ₜ* ZHatMul where
  toFun z := Multiplicative.ofAdd (zHatMulNat n z.toAdd)
  map_one' := by
    apply Multiplicative.ext
    simp [zHatMulNat]
  map_mul' x y := by
    apply Multiplicative.ext
    exact nsmul_add x.toAdd y.toAdd n
  continuous_toFun := map_continuous (zHatMulNat n)


end
end Langlands.NYLL.ClassFormation
