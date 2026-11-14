/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/


/-
Modified by Worker 640 on 2026-11-14: extracted the proof of M144.034
from NormalBasisLattice.lean at fbd320cd8b1b06487c58227e92eb135794267709,
prefixed the namespace with Langlands.NYLL, reduced imports, and stated the
result using the published proposition target. Local prerequisite adaptations
are documented in the paired Markdown. LICENSE and NOTICE remain in licenses/NYLL/.
-/

import Langlands.NYLL.GaloisCohomology.Cyclic.Herbrand.NormalBasisLattice.U029.Statements

namespace Langlands.NYLL.CyclicCohomology

universe u

open scoped ValuativeRel
open Filter

variable (L : Type u) [Field L]

/-- The finite geometric inverse identity for the correction sum. -/
theorem one_add_mul_one_add_inverseCorrectionPartialSum (x : L) (d : Nat) :
    one_add_mul_one_add_inverseCorrectionPartialSumStatement (L := L) x d := by
  unfold one_add_mul_one_add_inverseCorrectionPartialSumStatement
  have hgeom : 1 + inverseCorrectionPartialSum (L := L) x d =
      (Finset.range (d + 1)).sum fun i => (-x) ^ i := by
    induction d with
    | zero => simp [inverseCorrectionPartialSum]
    | succ d ih =>
        have hsucc :
            inverseCorrectionPartialSum (L := L) x (d + 1) =
              inverseCorrectionPartialSum (L := L) x d + (-x) ^ (d + 1) := by
          simp [inverseCorrectionPartialSum, Finset.sum_range_succ]
        rw [hsucc, Finset.sum_range_succ, ← ih]
        simp [add_assoc]
  rw [hgeom]
  simpa [sub_neg_eq_add] using
    (mul_neg_geom_sum (x := (-x : L)) (n := d + 1))

end Langlands.NYLL.CyclicCohomology
