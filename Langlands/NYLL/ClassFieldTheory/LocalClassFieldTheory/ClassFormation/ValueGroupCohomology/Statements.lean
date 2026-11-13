/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

/-
Modified by Worker 230, 13 November 2026: extract M141.001–.003 from
upstream fbd320cd8b1b06487c58227e92eb135794267709, prefix namespaces by
Langlands.NYLL, and reduce imports. Data bodies and their local instance
scope are unchanged; theorems become Prop-valued definitions with the
Statement suffix and the source propositions as their bodies. See the
paired Markdown; LICENSE and NOTICE remain under licenses/NYLL/.
-/

import Langlands.NYLL.ClassFieldTheory.LocalClassFieldTheory.ClassFormation.ValueGroupCohomology.Definitions

namespace Langlands.NYLL.LocalClassFieldTheory

open Langlands.NYLL.LocalFieldTheory
open Langlands.NYLL.CyclicCohomology

noncomputable section

open scoped BigOperators

universe u

open Langlands.NYLL.CyclicCohomology.ProfiniteCohomology.Herbrand

variable (K L : Type u) [Field K] [Field L] [Algebra K L]
  [FiniteDimensional K L]

def galoisGroupValueGroup_tateNorm_toAddStatement (a : Multiplicative Int) : Prop :=
    letI := galoisGroupValueGroupMulDistribMulAction K L
    Multiplicative.toAdd
        (tateNorm (Gal(L / K)) (Multiplicative Int) a) =
      (Fintype.card (Gal(L / K)) : Int) * Multiplicative.toAdd a

def galoisGroupValueGroupFixedToZModHom_surjectiveStatement : Prop :=
    letI := galoisGroupValueGroupMulDistribMulAction K L
    Function.Surjective (galoisGroupValueGroupFixedToZModHom K L)

end
end Langlands.NYLL.LocalClassFieldTheory
