/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

/-
Modifications by Worker 85, 14 November 2026:
State only the theorem M250.005 (lines 80–86) of
Nyll/ClassFieldTheory/LocalClassFieldTheory/Finite/LocalReciprocity/
FiniteSubgroupResidueDegree.lean
at fbd320cd8b1b06487c58227e92eb135794267709, without its proof, as the
closed proposition localAbstractFixedDecompositionGroup_eq_topStatement.
The section variable K and its instance binders (lines 33–34) become leading
universal binders, followed by the theorem's own binder H. Add the
Langlands.NYLL namespace prefix, also in the opened namespace, and the suffix
Statement. Import the Library modules that publish
localSeparableValuationSubring, abstractFixedField and decompositionGroup
instead of the source imports. Omit the noncomputable section, the open lines
this statement does not need and all other declarations. The original
LICENSE and NOTICE are retained in licenses/NYLL/.
-/

import Langlands.NYLL.ClassFieldTheory.LocalClassFieldTheory.Finite.LocalReciprocity.LocalResidueDatum.U006.Definitions
import Langlands.NYLL.ClassFieldTheory.LocalClassFieldTheory.Finite.LocalReciprocity.FiniteAbstractFixedField.Initial.Definitions
import Langlands.NYLL.ValuedFieldTheory.Ramification.HilbertRamification.ValuationSubring.Definitions

/-!
# Full decomposition group over the fixed field of a closed subgroup: target

A closed proposition about a nonarchimedean local field `K` and a closed
subgroup `H` of the Galois group of `SeparableClosure K` over `K`: the
decomposition group of the chosen valuation ring of `SeparableClosure K`
over the fixed field of `H` is the whole group of automorphisms of
`SeparableClosure K` over that fixed field.
-/

namespace Langlands.NYLL.LocalClassFieldTheory

open Langlands.NYLL.RamificationTheory.HilbertRamification.ValuationSubring

/-- Every automorphism over the fixed field preserves the selected extension
valuation.  This is the base-change form of the full decomposition-group
statement proved for `K`. -/
def localAbstractFixedDecompositionGroup_eq_topStatement : Prop :=
  ∀ (K : Type) [Field K] [ValuativeRel K] [TopologicalSpace K]
    [IsNonarchimedeanLocalField K]
    (H : ClosedSubgroup (Gal(SeparableClosure K/K))),
    decompositionGroup (abstractFixedField K (SeparableClosure K) H)
      (localSeparableValuationSubring K) = ⊤

end Langlands.NYLL.LocalClassFieldTheory
