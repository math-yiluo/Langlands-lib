/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

/-
Modified by Worker 294, 2026-11-14: focused extraction of the indicated
M353 source units, namespace qualification, source-private name adaptation,
and replacement of the recursive imports by focused published dependencies.
Prepared for exact proof submission by Worker 241, 2026-11-16, reusing
Worker 294's source-adapted proof without mathematical changes.
The accompanying Markdown records exact source correspondence and edits.
License and notices are retained in licenses/NYLL/.
-/

import Langlands.NYLL.ClassFieldTheory.LubinTate.FormalModule.RecursiveIntertwiner.Replacement.ListStatements

universe u v w

namespace Langlands.NYLL.PortInternal.M353

open Langlands.NYLL.LocalFieldTheory.DiscreteValuationField
open Langlands.NYLL.LubinTate.SameUniformizer

variable {K : Type u} [Field K]
variable {F : LocalField.{u, v} K}
variable {sigma : Type w} [Fintype sigma]

theorem d034
    {L : sigma → F.valuationSubring}
    {m : ℕ} (hm : 2 ≤ m)
    (target : MvPowerSeries sigma F.valuationSubring)
    (ds : List {d : sigma →₀ ℕ // d.degree = m})
    (H : d002 (F := F) L)
    (q : sigma →₀ ℕ) (hq : q.degree < m) :
    d034Statement hm target ds H q hq := by
  change MvPowerSeries.coeff q (d031 hm target ds H).1 =
      MvPowerSeries.coeff q H.1
  induction ds generalizing H with
  | nil => rfl
  | cons d ds ih =>
      have hqd : q ≠ d.1 := by
        intro h
        have hdegree :=
          congrArg (fun x : sigma →₀ ℕ => x.degree) h
        omega
      calc
        MvPowerSeries.coeff q
              (d031 hm target (d :: ds) H).1 =
            MvPowerSeries.coeff q
              (d031 hm target ds
                (d030 hm target H d)).1 := by
              rfl
        _ = MvPowerSeries.coeff q
              (d030 hm target H d).1 :=
          ih (d030 hm target H d)
        _ = MvPowerSeries.coeff q H.1 := by
          simp [d030,
            MvPowerSeries.coeff_monomial_ne hqd]

end Langlands.NYLL.PortInternal.M353
