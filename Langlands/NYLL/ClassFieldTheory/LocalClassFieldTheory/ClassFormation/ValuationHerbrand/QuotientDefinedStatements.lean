/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

/-
Modified by Worker 230, 16 November 2026: extract M142.002 from upstream
fbd320cd8b1b06487c58227e92eb135794267709, prefix the namespace with
Langlands.NYLL, replace imports by published dependencies, and represent
the source theorem statement as a Prop-valued definition. Source Type
universes, complete telescope, binder kinds and local-instance scope are
retained. See the paired Markdown and licenses/NYLL/LICENSE and NOTICE.
-/

import Langlands.NYLL.ClassFieldTheory.LocalClassFieldTheory.ClassFormation.Valuation.IntegerDefinitions
import Langlands.NYLL.ClassFieldTheory.LocalClassFieldTheory.ClassFormation.Valuation.Definitions
import Langlands.NYLL.GaloisCohomology.Cyclic.Herbrand.HerbrandFiniteness.Definitions

namespace Langlands.NYLL.LocalClassFieldTheory

open Langlands.NYLL.LocalFieldTheory
open Langlands.NYLL.CyclicCohomology

noncomputable section

open scoped ValuativeRel
open Langlands.NYLL.CyclicCohomology.ProfiniteCohomology.Herbrand
open Langlands.NYLL.LocalFieldTheory.IsNonarchimedeanLocalField

variable (K L : Type) [Field K] [ValuativeRel K]
  [Field L] [ValuativeRel L] [TopologicalSpace L]
  [IsNonarchimedeanLocalField L] [Algebra K L] [FiniteDimensional K L]
  [Valuation.HasExtension (ValuativeRel.valuation K) (ValuativeRel.valuation L)]
  [IsIntegralClosure (ValuativeRel.valuation L).integer
    (ValuativeRel.valuation K).integer L]

omit [ValuativeRel K] [ValuativeRel L] [TopologicalSpace L]
    [IsNonarchimedeanLocalField L]
    [Valuation.HasExtension (ValuativeRel.valuation K) (ValuativeRel.valuation L)]
    [IsIntegralClosure (ValuativeRel.valuation L).integer
      (ValuativeRel.valuation K).integer L] in
def galoisGroupValueGroup_herbrandQuotientDefinedStatement
    (g : Gal(L/K)) : Prop :=
    letI := galoisGroupValueGroupMulDistribMulAction K L
    HerbrandQuotientDefined (Gal(L / K)) (Multiplicative Int) g

end
end Langlands.NYLL.LocalClassFieldTheory
