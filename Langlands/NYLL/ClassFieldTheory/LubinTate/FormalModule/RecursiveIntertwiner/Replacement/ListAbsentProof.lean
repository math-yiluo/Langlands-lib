/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

/-
Prepared by Worker 294, 2026-11-14: source-adapted extraction of M353.035,
namespace qualification, source-private name adaptation, and focused imports.
Prepared for publication by Worker 662, 2026-11-16: source and telescope
comparison, expanded provenance and attribution, and published-input validation.
The accompanying Markdown records exact source correspondence and adaptations.
License and notices are retained in licenses/NYLL/.
-/

import Langlands.NYLL.ClassFieldTheory.LubinTate.FormalModule.RecursiveIntertwiner.Replacement.ListStatements
import Langlands.NYLL.ClassFieldTheory.LubinTate.FormalModule.RecursiveIntertwiner.Replacement.StepOtherProof

universe u v w

namespace Langlands.NYLL.PortInternal.M353

open Langlands.NYLL.LocalFieldTheory.DiscreteValuationField
open Langlands.NYLL.LubinTate.SameUniformizer

variable {K : Type u} [Field K]
variable {F : LocalField.{u, v} K}
variable {sigma : Type w} [Fintype sigma]

theorem d035
    {L : sigma → F.valuationSubring}
    {m : ℕ} (hm : 2 ≤ m)
    (target : MvPowerSeries sigma F.valuationSubring)
    (ds : List {d : sigma →₀ ℕ // d.degree = m})
    (H : d002 (F := F) L)
    (q : {d : sigma →₀ ℕ // d.degree = m})
    (hq : q ∉ ds) :
    d035Statement hm target ds H q hq := by
  change MvPowerSeries.coeff q.1 (d031 hm target ds H).1 =
      MvPowerSeries.coeff q.1 H.1
  induction ds generalizing H with
  | nil => rfl
  | cons d ds ih =>
      have hqd : q ≠ d := by
        intro h
        apply hq
        simp [h]
      have hqds : q ∉ ds := by
        intro h
        exact hq (List.mem_cons_of_mem d h)
      calc
        MvPowerSeries.coeff q.1
              (d031 hm target (d :: ds) H).1 =
            MvPowerSeries.coeff q.1
              (d031 hm target ds
                (d030 hm target H d)).1 := by
              rfl
        _ = MvPowerSeries.coeff q.1
              (d030 hm target H d).1 :=
          ih (d030 hm target H d) hqds
        _ = MvPowerSeries.coeff q.1 H.1 :=
          d033
            hm target H q d hqd

end Langlands.NYLL.PortInternal.M353
