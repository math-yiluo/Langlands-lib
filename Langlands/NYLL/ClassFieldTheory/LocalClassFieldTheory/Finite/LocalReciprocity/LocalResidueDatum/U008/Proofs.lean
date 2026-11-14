/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)

Modified by Worker 3, 2026-11-13: adapt the Prop-valued instance M249.008,
lines 106–113 of
Nyll/ClassFieldTheory/LocalClassFieldTheory/Finite/LocalReciprocity/LocalResidueDatum.lean
at upstream commit fbd320cd8b1b06487c58227e92eb135794267709, to prove the
published closed target localSeparableValuationHasExtensionStatement; prefix
the namespace with Langlands.NYLL; declare it as a theorem and register it
with `attribute [instance]`; replace the source imports by the published
statement and the published Chevalley pullback theorem; replace the cited
theorem localSeparableValuationSubring_pullback (M249.007, lines 94–104) by
its source proof inline, with the private lemma M249.004 (lines 66–76)
inlined as a `have` and the local instances M249.001/M249.002 installed from
their published names. The retained license and notices are in licenses/NYLL/.
-/

import Langlands.NYLL.ClassFieldTheory.LocalClassFieldTheory.Finite.LocalReciprocity.LocalResidueDatum.U008.Statements
import Langlands.NYLL.ValuedFieldTheory.Valuation.DiscreteValuationField.ChevalleyExtension.U004.Proofs

/-!
# The chosen separable valuation extends the local valuation

The proof of the NYLL M249.008 instance for the exact published closed target,
registered as a global instance as in the source.
-/

noncomputable section

namespace Langlands.NYLL.LocalClassFieldTheory

open Langlands.NYLL.LocalFieldTheory

attribute [local instance] Langlands.NYLL.PortInternal.M249.d001
  Langlands.NYLL.PortInternal.M249.d002

/-- The valuation on the separable closure extends the base discrete valuation. -/
theorem localSeparableValuationHasExtension :
    localSeparableValuationHasExtensionStatement := by
  intro K _ _ _ _
  exact (open Langlands.NYLL.ValuationTheory.DiscreteValuationField.Valuation in
    hasExtension_valuation_of_valuationSubring_pullback)
    (localCompleteDVF K).valuation (localSeparableValuationSubring K)
      (fun x => by
        -- The source theorem `localSeparableValuationSubring_pullback` (M249.007),
        -- proved inline as in the source, with its private lemma M249.004.
        have habsolute : ∀ y : K,
            algebraMap K (AlgebraicClosure K) y ∈
                Langlands.NYLL.PortInternal.M249.d003 K ↔
              y ∈ (localCompleteDVF K).valuation.valuationSubring := by
          intro y
          rcases Classical.choose_spec
              (Langlands.NYLL.ValuationTheory.DiscreteValuationField.Valuation.exists_extension_valuationSubring
                (L := AlgebraicClosure K) (localCompleteDVF K).valuation) with
            ⟨_hmap, _hlocal, hpullback⟩
          exact hpullback y
        change algebraMap (SeparableClosure K) (AlgebraicClosure K)
            (algebraMap K (SeparableClosure K) x) ∈
              Langlands.NYLL.PortInternal.M249.d003 K ↔ _
        rw [← IsScalarTower.algebraMap_apply K (SeparableClosure K)
          (AlgebraicClosure K)]
        exact habsolute x)

attribute [instance] localSeparableValuationHasExtension

end Langlands.NYLL.LocalClassFieldTheory

end
