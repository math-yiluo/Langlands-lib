/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

/-
Modified by Worker 230, 16 November 2026: extract M143.001 from upstream
fbd320cd8b1b06487c58227e92eb135794267709, prefix the namespace with
Langlands.NYLL, replace imports by published dependencies, and represent
the source theorem statement as a Prop-valued definition. Source Type
universes, complete telescope, binder kinds and local-instance scope are
retained. See the paired Markdown and licenses/NYLL/LICENSE and NOTICE.
-/

import Mathlib.SetTheory.Cardinal.Finite
import Mathlib.RepresentationTheory.Homological.GroupCohomology.Hilbert90
import Mathlib.RepresentationTheory.Homological.TateCohomology.Basic
import Langlands.NYLL.ClassFieldTheory.LocalClassFieldTheory.ClassFormation.Valuation.IntegerDefinitions
import Langlands.NYLL.GaloisCohomology.Cyclic.Herbrand.HerbrandFiniteness.Definitions
import Langlands.NYLL.ValuedFieldTheory.LocalField.NonarchimedeanLocalField.ValuationExactSequence.Definitions

namespace Langlands.NYLL.LocalClassFieldTheory

open Langlands.NYLL.LocalFieldTheory
open Langlands.NYLL.CyclicCohomology

noncomputable section

open scoped ValuativeRel
open Langlands.NYLL.CyclicCohomology.ProfiniteCohomology.Herbrand
open Langlands.NYLL.LocalFieldTheory.IsNonarchimedeanLocalField

set_option linter.unusedVariables false in
def unitsTateH0FiniteOfIntegerUnitsHerbrandStatement
    (K L : Type) [Field K] [ValuativeRel K]
    [Field L] [ValuativeRel L] [TopologicalSpace L]
    [IsNonarchimedeanLocalField L] [Algebra K L] [FiniteDimensional K L]
    [Valuation.HasExtension (ValuativeRel.valuation K) (ValuativeRel.valuation L)]
    [IsIntegralClosure (ValuativeRel.valuation L).integer
      (ValuativeRel.valuation K).integer L]
    (g : Gal(L/K))
    (hg : ∀ σ : Gal(L / K), σ ∈ Subgroup.zpowers g)
    (hU :
      letI := galoisGroupIntegerUnitsMulDistribMulActionOfIsIntegralClosure K L
      HerbrandQuotientDefined (Gal(L / K))
        (ValuativeRel.valuation L).integerˣ g) : Prop :=
    Finite (tateCohomology (Rep.ofAlgebraAutOnUnits K L) 0)

end
end Langlands.NYLL.LocalClassFieldTheory
