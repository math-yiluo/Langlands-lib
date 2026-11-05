/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)

Modified by Worker 1556, 2026-11-04, with statement design, source extraction
and reuse analysis contributed by Worker 106: extract the statements of
M328.001 and M328.002 from upstream commit
fbd320cd8b1b06487c58227e92eb135794267709, close their common Type 0
telescope around their lower-then-upper conjunction, prefix namespaces
with Langlands.NYLL and use the two focused published data imports.
Retained license and notices: licenses/NYLL/.
-/

import Langlands.NYLL.ValuedFieldTheory.Ramification.LocalField.Core.Definitions
import Langlands.NYLL.ValuedFieldTheory.LocalField.NonarchimedeanLocalField.ResidueGalois.AlgebraDefinitions

/-!
# Zero-depth local ramification groups and the actual residue-action kernel

The closed proposition extracted from NYLL M328.001 and M328.002 retains
both actual ramification groups, the actual supplied residue action and
the complete common source telescope. It is a statement target.
-/

namespace Langlands.NYLL.RamificationTheory.LocalField

open Langlands.NYLL.LocalFieldTheory
open scoped ValuativeRel

/-- The zeroth lower and upper local ramification groups are the kernel of
the actual residue-field algebra action, under the full source hypotheses. -/
def LocalRamificationZeroResidueKernelStatement : Prop :=
  ∀ (K L : Type)
    [Field K] [ValuativeRel K] [TopologicalSpace K]
    [IsNonarchimedeanLocalField K]
    [Field L] [ValuativeRel L] [TopologicalSpace L]
    [IsNonarchimedeanLocalField L]
    [Algebra K L] [FiniteDimensional K L] [IsGalois K L]
    [Valuation.HasExtension
      (ValuativeRel.valuation K) (ValuativeRel.valuation L)]
    [IsIntegralClosure 𝒪[L] 𝒪[K] L]
    [Module.Finite 𝒪[K] 𝒪[L]],
    (localLowerRamificationGroup K L 0 =
      (galoisGroupResidueAlgEquivHomOfIsIntegralClosure K L).ker) ∧
    (localUpperRamificationGroup K L 0 =
      (galoisGroupResidueAlgEquivHomOfIsIntegralClosure K L).ker)

end Langlands.NYLL.RamificationTheory.LocalField
