/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

/-
Modifications by Worker 9, 13 November 2026 UTC:
Extract only the proof of M075.028 from
Nyll/ClassFieldTheory/AbstractClassFieldTheory/Reciprocity/Core.lean at
fbd320cd8b1b06487c58227e92eb135794267709. Add the Langlands.NYLL
namespace prefix and import only the published Core.ZHat.Statements
module. State the theorem as the published Statement applied to the source
parameters. In the first calc step replace the citation
(zHatReduction_int n hn (k : ℤ)).symm of the unpublished M009.007 lemma by
rfl, which is that lemma's own source proof
(Nyll/GaloisCohomology/ProfiniteIntegers/ProfiniteInteger.lean, lines
112-116). The proof is otherwise the original one line for line. The
original LICENSE and NOTICE are retained in licenses/NYLL/.
-/

import Langlands.NYLL.ClassFieldTheory.AbstractClassFieldTheory.Reciprocity.Core.ZHat.Statements

/-!
# A profinite-integer step: `n z = k` with `0 ≤ k < n` forces `k = 0`

The exact proof, by reduction modulo `n`, that a natural number `k < n`
whose image in `ℤ̂` is divisible by `n` must vanish.
-/

namespace Langlands.NYLL.ClassFormation

/-- An elementary profinite-integer step:
if `n z = k` in `ℤ̂`, with `0 ≤ k < n`, then `k = 0`. -/
theorem abstractReciprocity_zHat_nsmul_eq_natCast_forces_zero
    (n k : ℕ) (hn : 0 < n) (hk : k < n) (z : ZHat)
    (h : n • z =
      Int.castRingHom ZHat (k : ℤ)) :
    abstractReciprocity_zHat_nsmul_eq_natCast_forces_zeroStatement n k hn hk z h := by
  have hkmod : (k : ZMod n) = 0 := by
    have hkmodInt : ((k : ℤ) : ZMod n) = 0 := by
      calc
        ((k : ℤ) : ZMod n) = zHatReduction n hn
          (Int.castRingHom ZHat (k : ℤ)) := rfl
        _ =
          zHatReduction n hn (n • z) := congrArg (zHatReduction n hn) h.symm
        _ = n • zHatReduction n hn z := map_nsmul (zHatReduction n hn) n z
        _ = 0 := by rw [nsmul_eq_mul, ZMod.natCast_self, zero_mul]
    simpa using hkmodInt
  exact Nat.eq_zero_of_dvd_of_lt
    ((ZMod.natCast_eq_zero_iff k n).1 hkmod) hk

end Langlands.NYLL.ClassFormation
