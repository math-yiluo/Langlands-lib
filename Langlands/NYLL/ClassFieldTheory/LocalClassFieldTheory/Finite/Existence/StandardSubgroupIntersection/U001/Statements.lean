/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

/-
Modified by Worker 346, 13 November 2026: extract the type of M403.001
(StandardSubgroupIntersection.lean, lines 37–44) from upstream commit
fbd320cd8b1b06487c58227e92eb135794267709; prefix the namespace with
Langlands.NYLL and close the complete universe-polymorphic theorem
telescope as a Prop-valued definition with a Statement suffix. The proof
is omitted and the source imports are replaced by the published
valuation-divisibility and standard-subgroup definitions. See the paired
Markdown for details.
The original LICENSE and NOTICE remain in licenses/NYLL/.
-/

import Langlands.NYLL.ClassFieldTheory.LocalClassFieldTheory.Finite.Existence.UnramifiedNormSubgroup.U011.Definitions
import Langlands.NYLL.ValuedFieldTheory.LocalField.NonarchimedeanLocalField.StandardOpenSubgroups.UniformizerPrincipalSubgroup

/-!
# Intersecting standard norm conditions: proposition target

Source: M403.001, lines 37–44 of
`Nyll/ClassFieldTheory/LocalClassFieldTheory/Finite/Existence/StandardSubgroupIntersection.lean`.
-/

namespace Langlands.NYLL.LocalClassFieldTheory

open scoped ValuativeRel
open LocalFieldTheory
open LocalFieldTheory.IsNonarchimedeanLocalField

/-- The intersection of the unramified valuation condition and the
principal-unit condition is contained in the corresponding standard subgroup. -/
def unramifiedNormSubgroup_inf_uniformizerPrincipalSubgroup_leStatement.{u} : Prop :=
  ∀ (K : Type u) [Field K] [ValuativeRel K] [TopologicalSpace K]
    [IsNonarchimedeanLocalField K]
    (ϖ : Kˣ) (d n : Nat)
    (_hϖ : valuationMap K (Additive.ofMul ϖ) = 1),
    unramifiedNormSubgroup K d ⊓
        LocalFieldTheory.uniformizerPrincipalSubgroup K ϖ 1 n ≤
      LocalFieldTheory.uniformizerPrincipalSubgroup K ϖ d n

end Langlands.NYLL.LocalClassFieldTheory
