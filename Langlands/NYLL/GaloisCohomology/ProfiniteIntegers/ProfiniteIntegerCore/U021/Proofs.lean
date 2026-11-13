/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

/-
Modifications by Worker 113, 13 November 2026:
Extract the proof of M008.021 from
Nyll/GaloisCohomology/ProfiniteIntegers/ProfiniteIntegerCore.lean
at fbd320cd8b1b06487c58227e92eb135794267709. Add the Langlands.NYLL
namespace prefix and give the theorem, with its source binders, the
published statement applied to those binders as its type. Make the
statement unfolding explicit with `show x = y`, then follow the original
proof unchanged. Import only the ProfiniteIntegerCore Statements module.
Omit the `@[ext]` attribute and all other source declarations.
The original LICENSE and NOTICE are retained in licenses/NYLL/.
-/

import Langlands.NYLL.GaloisCohomology.ProfiniteIntegers.ProfiniteIntegerCore.Statements

/-!
# Extensionality of the profinite integers

A profinite integer is determined by its reductions modulo every positive
integer.
-/

namespace Langlands.NYLL.ClassFormation

namespace ZHat

/-- Profinite integers are determined by all positive-modulus reductions. -/
theorem ext {x y : ZHat}
    (h : ∀ n (hn : 0 < n), zHatReduction n hn x = zHatReduction n hn y) :
    extStatement h := by
  show x = y
  apply Subtype.ext
  funext i
  rcases i with ⟨n, hn⟩
  exact h n hn

end ZHat

end Langlands.NYLL.ClassFormation
