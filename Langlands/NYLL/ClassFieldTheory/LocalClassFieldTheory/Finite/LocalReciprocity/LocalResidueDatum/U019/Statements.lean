/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)

Adapted by Worker 85, 14 November 2026: the type of the private source theorem
LocalClassFieldTheory.localSeparableResidueAlgAction_continuous (inventory
M249.019) becomes the closed proposition target
Langlands.NYLL.PortInternal.M249.d019Statement, quantified over the source
section variables. The proof is omitted (it is a separate proof unit). The
NYLL imports are replaced by the published modules defining
residueAlgActionOfEqTop and proving localSeparableDecompositionGroup_eq_top;
the source opens are reduced to the one this statement uses. All other source
declarations are omitted. The retained license and notice are
licenses/NYLL/LICENSE and licenses/NYLL/NOTICE.
-/

import Langlands.NYLL.ClassFieldTheory.LocalClassFieldTheory.Finite.LocalReciprocity.ResidueActionIndex.U003.Definitions
import Langlands.NYLL.ClassFieldTheory.LocalClassFieldTheory.Finite.LocalReciprocity.LocalResidueDatum.U010.Proofs

/-!
# Continuity of the local residue action: proposition target

Source: Naganori Yamaguchi, ClassFieldTheory, commit
fbd320cd8b1b06487c58227e92eb135794267709,
`Nyll/ClassFieldTheory/LocalClassFieldTheory/Finite/LocalReciprocity/LocalResidueDatum.lean`,
lines 31–46 (namespace, opens and section variables) and 319–327 (inventory
M249.019, docstring and type).
-/

namespace Langlands.NYLL.PortInternal.M249

open Langlands.NYLL.LocalClassFieldTheory

/-- Reduction from the absolute Galois group to the absolute Galois group of
the residue field is continuous for the Krull topologies.  A finite residue
subextension is controlled by adjoining to `K` one lift of each of its
finitely many elements. -/
def d019Statement : Prop :=
  ∀ (K : Type) [Field K] [ValuativeRel K] [TopologicalSpace K]
    [IsNonarchimedeanLocalField K],
    Continuous
      (residueAlgActionOfEqTop K
        (localSeparableValuationSubring K)
        (localSeparableDecompositionGroup_eq_top K))

end Langlands.NYLL.PortInternal.M249
