/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)

Modified by Worker 296, 2026-11-13: prove the published closed target for
M329.002 from NYLL commit fbd320cd8b1b06487c58227e92eb135794267709.
Prefix the namespace, use focused published imports, derive the needed
antitone comparison directly, and replace the source's private lower-zero
helper by the published upper-zero kernel identity and residue bijectivity.
Use the chosen extension witness locally; add no global instance.
Retained license and notices: licenses/NYLL/LICENSE and licenses/NYLL/NOTICE.
-/

import Langlands.NYLL.ValuedFieldTheory.Ramification.LocalField.Unramified.Statement
import Langlands.NYLL.ValuedFieldTheory.Ramification.LocalField.ResidueInertia.Proofs
import Langlands.NYLL.ValuedFieldTheory.LocalField.NonarchimedeanLocalField.FiniteUnramified.ResidueBijectiveProof
import Langlands.NYLL.ValuedFieldTheory.Ramification.HilbertRamification.HerbrandFunction.LawsProof

namespace Langlands.NYLL.RamificationTheory.LocalField

open Langlands.NYLL.LocalFieldTheory
open Langlands.NYLL.RamificationTheory.HilbertRamification

/-- Every nonnegative upper ramification group of an actual unramified
finite Galois extension of local fields is trivial. -/
theorem localUpperRamificationGroup_eq_bot_of_unramifiedValuation :
    localUpperRamificationGroup_eq_bot_of_unramifiedValuationStatement := by
  intro K L _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ t ht
  apply le_antisymm
  · calc
      localUpperRamificationGroup K L t ≤ localUpperRamificationGroup K L 0 := by
        let : _root_.Valuation.HasExtension (localCompleteDVF K).valuation
            (chosenLocalExtensionCompleteDVF K L).valuation :=
          Classical.choose (chosenLocalExtension_properties K L)
        unfold localUpperRamificationGroup
        apply Higher.lowerRamificationGroup_antitone
          (chosenLocalExtension_uniqueValuationExtension.{0} K L)
        exact (Higher.inverseHerbrandFunctionOfUniqueExtension_strictMono
          (chosenLocalExtension_uniqueValuationExtension.{0} K L)).monotone ht
      _ = (galoisGroupResidueAlgEquivHomOfIsIntegralClosure K L).ker :=
        localUpperRamificationGroup_zero_eq_residue_ker K L
      _ = ⊥ := (MonoidHom.ker_eq_bot_iff _).mpr
        (galoisGroupResidueAlgEquivHomOfIsIntegralClosure_bijective_of_unramifiedValuation
          K L).1
  · exact bot_le

end Langlands.NYLL.RamificationTheory.LocalField
