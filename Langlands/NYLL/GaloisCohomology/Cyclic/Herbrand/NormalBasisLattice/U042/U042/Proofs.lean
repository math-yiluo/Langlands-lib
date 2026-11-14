/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

/-
Modified by Worker 640 on 2026-11-14: extracted M144.042 from
NormalBasisLattice.lean at fbd320cd8b1b06487c58227e92eb135794267709,
prefixed the namespace with Langlands.NYLL, reduced imports, and stated the
result using the published proposition target. LICENSE and NOTICE remain
in licenses/NYLL/.
-/

import Langlands.NYLL.GaloisCohomology.Cyclic.Herbrand.NormalBasisLattice.U042.Statements
import Langlands.NYLL.ValuedFieldTheory.LocalField.NonarchimedeanLocalField.IdealQuotients.U006.Proofs

namespace Langlands.NYLL.CyclicCohomology

universe u

open scoped ValuativeRel
open LocalFieldTheory

variable (K L : Type u) [Field K] [Field L] [Algebra K L]
  [ValuativeRel K] [TopologicalSpace K] [IsNonarchimedeanLocalField K]
  [ValuativeRel L]
  [Valuation.HasExtension (ValuativeRel.valuation K) (ValuativeRel.valuation L)]

/-- The chosen base uniformizer maps into the extension valuation ring's maximal ideal. -/
theorem integerRingMap_uniformizer_mem_maximalIdeal_of_valuationExtension :
    integerRingMap_uniformizer_mem_maximalIdeal_of_valuationExtensionStatement K L := by
  unfold integerRingMap_uniformizer_mem_maximalIdeal_of_valuationExtensionStatement
  have hπK :
      chosenIntegerRingUniformizer K ∈ (𝓂[K] : Ideal 𝒪[K]) := by
    rw [chosenIntegerRingUniformizer_maximalIdeal_eq K]
    exact Ideal.subset_span (Set.mem_singleton (chosenIntegerRingUniformizer K))
  exact (Valuation.HasExtension.algebraMap_mem_maximalIdeal_iff
    (ValuativeRel.valuation K) (ValuativeRel.valuation L)).2 hπK

end Langlands.NYLL.CyclicCohomology
