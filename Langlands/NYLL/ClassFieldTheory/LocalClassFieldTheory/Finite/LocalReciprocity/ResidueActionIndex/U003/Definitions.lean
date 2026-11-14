/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

/-
Modifications by Worker 85, 14 November 2026:
Extract only M244.003 (residueAlgActionOfEqTop, lines 61–70) from
Nyll/ClassFieldTheory/LocalClassFieldTheory/Finite/LocalReciprocity/
ResidueActionIndex.lean
at fbd320cd8b1b06487c58227e92eb135794267709. Add the Langlands.NYLL
namespace prefix, also in the opened namespace. Import the Library modules
that publish toDecompositionGroupOfEqTop and decompositionGroupResidueAction
instead of the source imports. Omit the open lines this definition does not
need and all other declarations. The noncomputable section, universes,
section variables, docstring, binders, type and body are otherwise the
source text.
The original LICENSE and NOTICE are retained in licenses/NYLL/.
-/

import Langlands.NYLL.ClassFieldTheory.LocalClassFieldTheory.Finite.LocalReciprocity.ResidueActionIndex.U001.Definitions
import Langlands.NYLL.ValuedFieldTheory.Ramification.HilbertRamification.ResidueExactSequence.ResidueAction

/-!
# The residue action of the whole Galois group

When the decomposition group of a valuation ring `A` of a Galois extension
`L / K` is the whole group, the residue action of the decomposition group on
the residue field of `A` becomes an action of the whole group
`L ≃ₐ[K] L`.
-/

namespace Langlands.NYLL.LocalClassFieldTheory

noncomputable section

universe u v

open Langlands.NYLL.RamificationTheory.HilbertRamification.ValuationSubring

variable (K : Type u) {L : Type v} [Field K] [Field L] [Algebra K L]
  [IsGalois K L]

/-- The residue action from the exact sequence, viewed on the whole Galois group
when the chosen extension valuation has full decomposition group. -/
noncomputable def residueAlgActionOfEqTop
    (A : _root_.ValuationSubring L)
    (hA : decompositionGroup K A = ⊤) :
    (L ≃ₐ[K] L) →*
      (selectedResidueField A ≃ₐ[decompositionResidueField K A]
        selectedResidueField A) :=
  (decompositionGroupResidueAction (K := K) A).comp
    (toDecompositionGroupOfEqTop K A hA)

end

end Langlands.NYLL.LocalClassFieldTheory
