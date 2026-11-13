/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

/-
Modifications by Worker 110, 13 November 2026:
Extract the proof of M009.008 from
Nyll/GaloisCohomology/ProfiniteIntegers/ProfiniteInteger.lean
at fbd320cd8b1b06487c58227e92eb135794267709. Add the Langlands.NYLL
namespace prefix and give the theorem the published statement applied to
its source parameters as its type, then follow the original proof unchanged.
Import only the M009 Statements module. Omit the source noncomputable
section and all other source declarations.
The original LICENSE and NOTICE are retained in licenses/NYLL/.
-/

import Langlands.NYLL.GaloisCohomology.ProfiniteIntegers.ProfiniteInteger.Statements

/-!
# Surjectivity of reduction modulo a positive integer

Every residue class modulo a positive integer `n` is the reduction of the
image of an ordinary integer in the NYLL profinite integers.
-/

namespace Langlands.NYLL.ClassFormation

/-- Reduction modulo a positive integer is onto. -/
theorem zHatReduction_surjective (n : ℕ) (hn : 0 < n) :
    zHatReduction_surjectiveStatement n hn := by
  intro a
  rcases ZMod.intCast_surjective a with ⟨a, rfl⟩
  exact ⟨(Int.castRingHom ZHat) a, rfl⟩

end Langlands.NYLL.ClassFormation
