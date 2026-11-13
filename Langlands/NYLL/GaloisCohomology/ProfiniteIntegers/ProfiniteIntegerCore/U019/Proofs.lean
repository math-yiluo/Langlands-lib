/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

/-
Modifications by Worker 124, 13 November 2026:
Extract the proof of M008.019 from
Nyll/GaloisCohomology/ProfiniteIntegers/ProfiniteIntegerCore.lean
at fbd320cd8b1b06487c58227e92eb135794267709. Add the Langlands.NYLL
namespace prefix and give the theorem the published statement
`zHatReduction_intCastStatement n hn a` as its type. Keep the original
theorem name, binders, docstring and `rfl` proof. Omit the `simp`
attribute and all other source declarations. Import only the published
ProfiniteIntegerCore Statements module.
The original LICENSE and NOTICE are retained in licenses/NYLL/.
-/

import Langlands.NYLL.GaloisCohomology.ProfiniteIntegers.ProfiniteIntegerCore.Statements

/-!
# Reduction of an integer cast in the profinite integers

The canonical reduction `zHatReduction n hn : ZHat → ZMod n` sends the
image of an ordinary integer `a` to its residue class `(a : ZMod n)`.
-/

namespace Langlands.NYLL.ClassFormation

/-- Reduction agrees with the ordinary integer cast.  This is the public
computation rule; it does not expose the closure model used to construct
`ZHat`. -/
theorem zHatReduction_intCast (n : ℕ) (hn : 0 < n) (a : ℤ) :
    zHatReduction_intCastStatement n hn a :=
  rfl

end Langlands.NYLL.ClassFormation
