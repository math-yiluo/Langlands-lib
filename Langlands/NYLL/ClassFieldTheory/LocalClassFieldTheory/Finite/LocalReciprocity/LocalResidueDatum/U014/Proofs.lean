/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)

Modified by Worker 370, 15 November 2026: adapt the Prop-valued instance
M249.014, lines 252–260 of
Nyll/ClassFieldTheory/LocalClassFieldTheory/Finite/LocalReciprocity/LocalResidueDatum.lean
at upstream commit fbd320cd8b1b06487c58227e92eb135794267709, to prove the
published closed target localDecompositionResidueFiniteStatement; prefix the
namespace and the opened namespaces with Langlands.NYLL; declare it as a
theorem, begin the proof with `intro` of the source section variables
(lines 45–46), and register it with `attribute [instance]`; keep the source
tactic body unchanged; replace the source imports by the published target and
the published module of localBaseResidueEquivDecompositionResidue; keep only
the opens the proof needs. The retained license and notices are in
licenses/NYLL/.
-/

import Langlands.NYLL.ClassFieldTheory.LocalClassFieldTheory.Finite.LocalReciprocity.LocalResidueDatum.U014.Statements
import Langlands.NYLL.ClassFieldTheory.LocalClassFieldTheory.Finite.LocalReciprocity.LocalResidueDatum.U011.Definitions

/-!
# The local decomposition residue field is finite

The proof of the NYLL M249.014 instance for the exact published closed target,
registered as a global instance as in the source.
-/

noncomputable section

namespace Langlands.NYLL.LocalClassFieldTheory

open Langlands.NYLL.LocalFieldTheory
open Langlands.NYLL.RamificationTheory.HilbertRamification.ValuationSubring

open scoped ValuativeRel

/-- The residue field attached to the local decomposition datum is finite. -/
theorem localDecompositionResidueFinite :
    localDecompositionResidueFiniteStatement := by
  intro K _ _ _ _
  have : Finite (localCompleteDVF K).residueField := by
    change Finite 𝓀[K]
    infer_instance
  exact Finite.of_equiv (localCompleteDVF K).residueField
    (localBaseResidueEquivDecompositionResidue K).toEquiv

attribute [instance] localDecompositionResidueFinite

end Langlands.NYLL.LocalClassFieldTheory

end
