/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

/-
Modifications by Worker 370, 14 November 2026, following the route that
Worker 85 checked:
Prove the published closed target of M249.010 from
Nyll/ClassFieldTheory/LocalClassFieldTheory/Finite/LocalReciprocity/
LocalResidueDatum.lean (lines 161-174) at
fbd320cd8b1b06487c58227e92eb135794267709. The section variable K and its
instance binders are introduced from the closed target. The source proof is
kept: it applies the published M249.009 proof to the translate of the chosen
ring, whose valuation extends the base valuation by the published
smul_hasExtension (M233.010) applied to the published M249.008 instance.
Add the Langlands.NYLL namespace prefix and import published Library modules
instead of the source imports.
The original LICENSE and NOTICE are retained in licenses/NYLL/.
-/

import Langlands.NYLL.ClassFieldTheory.LocalClassFieldTheory.Finite.LocalReciprocity.LocalResidueDatum.U008.Proofs
import Langlands.NYLL.ClassFieldTheory.LocalClassFieldTheory.Finite.LocalReciprocity.LocalResidueDatum.U009.Proofs
import Langlands.NYLL.ValuedFieldTheory.Ramification.GaloisValuation.AbsoluteGalois.FiniteLevelValuationRestriction.U010.Proofs

/-!
# Galois stability of the chosen valuation ring of the separable closure (NYLL M249.010)

The decomposition group of `localSeparableValuationSubring K` over a
nonarchimedean local field `K` is the whole group of `K`-algebra
automorphisms of `SeparableClosure K`: each automorphism carries the chosen
ring to a valuation ring whose valuation still extends the canonical
valuation of `K`, and that ring is the chosen one by M249.009.
-/

namespace Langlands.NYLL.LocalClassFieldTheory

open scoped Pointwise

open Langlands.NYLL.LocalFieldTheory
open Langlands.NYLL.RamificationTheory.HilbertRamification.ValuationSubring

/-- Every automorphism of the separable closure preserves the unique
extension of the Henselian local valuation. -/
theorem localSeparableDecompositionGroup_eq_top :
    localSeparableDecompositionGroup_eq_topStatement := by
  intro K _ _ _ _
  apply top_unique
  intro sigma _hsigma
  change sigma • localSeparableValuationSubring K =
    localSeparableValuationSubring K
  -- `smul_hasExtension` uses the published global instance
  -- `localSeparableValuationHasExtension` (M249.008) for the chosen ring.
  let : (localCompleteDVF K).valuation.HasExtension
      (sigma • localSeparableValuationSubring K).valuation :=
    Langlands.NYLL.RamificationTheory.ValuationSubring.smul_hasExtension
      (localCompleteDVF K).valuation (localSeparableValuationSubring K) sigma
  exact (localSeparableValuationSubring_eq_of_hasExtension K
    (sigma • localSeparableValuationSubring K)).symm

end Langlands.NYLL.LocalClassFieldTheory
