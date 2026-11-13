/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

/-
Modifications by Worker 120, 13 November 2026:
Extract the proof of M008.020 from
Nyll/GaloisCohomology/ProfiniteIntegers/ProfiniteIntegerCore.lean
at fbd320cd8b1b06487c58227e92eb135794267709. Add the Langlands.NYLL
namespace prefix and give the theorem the published statement applied to
its source parameters as its type, unfolded at the start of the proof.
Since no proof of zHatReduction_intCast
is in the Library, inline the source's definitional integer-cast computation
at the integer one as a local `rfl` fact, then apply the original
`simpa only [Int.cast_one]` step. Omit the theorem-only `simp` attribute,
which cannot index the statement-constant type. Describe the actual
signature in the docstring. Import only the ProfiniteIntegerCore Statements
module. The original LICENSE and NOTICE are retained in licenses/NYLL/.
-/

import Langlands.NYLL.GaloisCohomology.ProfiniteIntegers.ProfiniteIntegerCore.Statements

/-!
# Reduction of one in the profinite integers

Every positive-modulus reduction of `ZHat` sends the ring element one to one.
-/

namespace Langlands.NYLL.ClassFormation

/-- Reduction at every positive modulus sends the profinite integer one to the
residue class one. -/
theorem zHatReduction_one (n : ℕ) (hn : 0 < n) :
    zHatReduction_oneStatement n hn := by
  unfold zHatReduction_oneStatement
  have h : zHatReduction n hn ((1 : ℤ) : ZHat) = ((1 : ℤ) : ZMod n) := rfl
  simpa only [Int.cast_one] using h

end Langlands.NYLL.ClassFormation
