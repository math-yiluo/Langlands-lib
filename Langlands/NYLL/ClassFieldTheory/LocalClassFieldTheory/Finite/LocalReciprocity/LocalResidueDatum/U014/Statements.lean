/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

/-
Modifications by Worker 85, 14 November 2026:
State only the Prop-valued instances M249.014 (lines 252–255) and M249.016
(lines 268–271) of
Nyll/ClassFieldTheory/LocalClassFieldTheory/Finite/LocalReciprocity/
LocalResidueDatum.lean
at fbd320cd8b1b06487c58227e92eb135794267709, without their proofs, as the
closed propositions localDecompositionResidueFiniteStatement and
localSelectedResidueIsAlgClosedStatement. The section variable K and its
instance binders (lines 45–46) become leading universal binders. Each target
is an `abbrev`, so that a proof can be registered as an instance. Add the
Langlands.NYLL namespace prefix, also in the opened namespace, and the suffix
Statement. Import the Library modules that publish
localSeparableValuationSubring, decompositionResidueField and
selectedResidueField, and the Mathlib module of IsAlgClosed, instead of the
source imports. Omit the noncomputable section, the open lines these
statements do not need, the instance attributes and all other declarations.
The original LICENSE and NOTICE are retained in licenses/NYLL/.
-/

import Langlands.NYLL.ClassFieldTheory.LocalClassFieldTheory.Finite.LocalReciprocity.LocalResidueDatum.U006.Definitions
import Langlands.NYLL.ValuedFieldTheory.Ramification.HilbertRamification.ResidueExactSequence.Definitions
import Mathlib.FieldTheory.IsAlgClosed.Basic

/-!
# Residue fields of the chosen separable valuation ring: instance targets

Two closed propositions about the valuation ring
`localSeparableValuationSubring K` of `SeparableClosure K` chosen for a
nonarchimedean local field `K`: the residue field `κ` of its decomposition
field is finite, and its own residue field `λ` is algebraically closed.
-/

namespace Langlands.NYLL.LocalClassFieldTheory

open Langlands.NYLL.RamificationTheory.HilbertRamification.ValuationSubring

/-- Closed target for the NYLL M249.014 instance
`localDecompositionResidueFinite`: the residue field attached to the local
decomposition datum is finite. -/
abbrev localDecompositionResidueFiniteStatement : Prop :=
  ∀ (K : Type) [Field K] [ValuativeRel K] [TopologicalSpace K]
    [IsNonarchimedeanLocalField K],
    Finite (decompositionResidueField K
      (localSeparableValuationSubring K))

/-- Closed target for the NYLL M249.016 instance
`localSelectedResidueIsAlgClosed`: the selected residue field of the
separable valuation is algebraically closed. -/
abbrev localSelectedResidueIsAlgClosedStatement : Prop :=
  ∀ (K : Type) [Field K] [ValuativeRel K] [TopologicalSpace K]
    [IsNonarchimedeanLocalField K],
    IsAlgClosed (selectedResidueField
      (localSeparableValuationSubring K))

end Langlands.NYLL.LocalClassFieldTheory
