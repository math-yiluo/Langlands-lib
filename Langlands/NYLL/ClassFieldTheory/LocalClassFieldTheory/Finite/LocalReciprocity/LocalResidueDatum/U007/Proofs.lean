/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)

Modified by Worker 3, 2026-11-13: prove only M249.007 (source lines 94–104 of
Nyll/ClassFieldTheory/LocalClassFieldTheory/Finite/LocalReciprocity/LocalResidueDatum.lean
at upstream commit fbd320cd8b1b06487c58227e92eb135794267709) as
Langlands.NYLL.LocalClassFieldTheory.localSeparableValuationSubring_pullback,
whose type is the published localSeparableValuationSubring_pullbackStatement;
the source proof of the private lemma M249.004 (lines 66–76) is inlined as a
`have`; the two local instances M249.001/M249.002 are installed locally from
their published names. The retained license and notices are in licenses/NYLL/.
-/

import Langlands.NYLL.ClassFieldTheory.LocalClassFieldTheory.Finite.LocalReciprocity.LocalResidueDatum.U007.Statements

/-!
# Pullback of the chosen separable valuation ring: proof

Proof of NYLL M249.007.
-/

namespace Langlands.NYLL.LocalClassFieldTheory

attribute [local instance] Langlands.NYLL.PortInternal.M249.d001
  Langlands.NYLL.PortInternal.M249.d002

/-- Pulling the separable valuation subring back to `K` recovers the base valuation ring. -/
theorem localSeparableValuationSubring_pullback :
    localSeparableValuationSubring_pullbackStatement := by
  intro K _ _ _ _ x
  -- The private source lemma M249.004 (`localAbsoluteValuationSubring_pullback`).
  have habsolute : ∀ y : K,
      algebraMap K (AlgebraicClosure K) y ∈
          Langlands.NYLL.PortInternal.M249.d003 K ↔
        y ∈ (Langlands.NYLL.LocalFieldTheory.localCompleteDVF K).valuation.valuationSubring := by
    intro y
    rcases Classical.choose_spec
        (Langlands.NYLL.ValuationTheory.DiscreteValuationField.Valuation.exists_extension_valuationSubring
          (L := AlgebraicClosure K)
          (Langlands.NYLL.LocalFieldTheory.localCompleteDVF K).valuation) with
      ⟨_hmap, _hlocal, hpullback⟩
    exact hpullback y
  change algebraMap (SeparableClosure K) (AlgebraicClosure K)
      (algebraMap K (SeparableClosure K) x) ∈
        Langlands.NYLL.PortInternal.M249.d003 K ↔ _
  rw [← IsScalarTower.algebraMap_apply K (SeparableClosure K)
    (AlgebraicClosure K)]
  exact habsolute x

end Langlands.NYLL.LocalClassFieldTheory
