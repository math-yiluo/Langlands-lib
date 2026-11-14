/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

/-
Modifications by Worker 395, 14 November 2026 UTC:
Extract only the proof of M009.007 (zHatReduction_int) from
Nyll/GaloisCohomology/ProfiniteIntegers/ProfiniteInteger.lean (lines 110–116)
at fbd320cd8b1b06487c58227e92eb135794267709. Add the Langlands.NYLL
namespace prefix and import only the published ProfiniteInteger U007
Statements module. Keep the noncomputable section, the docstring, the theorem
name and binders, and state the theorem as the published
Statement applied to the source parameters. Omit the `simp` attribute,
because the stated type is the unexpanded proposition constant rather than an
equation, and all other source declarations. The original LICENSE and NOTICE
are retained in licenses/NYLL/.
Integrator replaces the duplicate reflexivity proof with the existing
M008.019 theorem `zHatReduction_intCast`, preserving the required M009.007 name.
-/

import Langlands.NYLL.GaloisCohomology.ProfiniteIntegers.ProfiniteInteger.U007.Statements
import Langlands.NYLL.GaloisCohomology.ProfiniteIntegers.ProfiniteIntegerCore.U019.Proofs

/-!
# Reduction of an integer in the profinite integers

The proof that reducing the image of an integer `a` in `ZHat` modulo a
positive `n` gives the residue class of `a` in `ZMod n`.
-/

namespace Langlands.NYLL.ClassFormation

noncomputable section

/-- Establishes the identity `zHatReduction n hn ((Int.castRingHom ZHat) a) = (a : ZMod n)`. -/
theorem zHatReduction_int (n : ℕ) (hn : 0 < n) (a : ℤ) :
    zHatReduction_intStatement n hn a :=
  zHatReduction_intCast n hn a

end

end Langlands.NYLL.ClassFormation
