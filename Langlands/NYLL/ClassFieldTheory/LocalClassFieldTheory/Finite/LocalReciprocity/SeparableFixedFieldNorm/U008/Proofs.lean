/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)

Modified by Worker 368, 15 November 2026: adapt the source theorem
LocalClassFieldTheory.relativeCosetAction_intermediateFieldUnit_val_of_isSeparable
(inventory M165.008, lines 178–197 of
Nyll/ClassFieldTheory/LocalClassFieldTheory/Finite/LocalReciprocity/SeparableFixedFieldNorm.lean
at upstream commit fbd320cd8b1b06487c58227e92eb135794267709) to prove the
published target
Langlands.NYLL.LocalClassFieldTheory.relativeCosetAction_intermediateFieldUnit_val_of_isSeparableStatement;
prefix the namespace with Langlands.NYLL; write the section variables left
by the source's `omit ... in` line as explicit binders; replace the source
imports by the published target. The tactic proof is the source's. The
retained license and notice are licenses/NYLL/LICENSE and
licenses/NYLL/NOTICE.
-/

import Langlands.NYLL.ClassFieldTheory.LocalClassFieldTheory.Finite.LocalReciprocity.SeparableFixedFieldNorm.U006.Statements

/-!
# Cosets of the base fixing subgroup: the coset action on units

The proof of the NYLL M165.008 theorem for the exact published target.
-/

namespace Langlands.NYLL.LocalClassFieldTheory
open RamificationTheory CyclicCohomology ClassFormation

/-- The abstract coset action on an `E`-unit is evaluation under the
corresponding actual `K`-embedding of `E`. -/
theorem relativeCosetAction_intermediateFieldUnit_val_of_isSeparable
    (K Ω : Type) [Field K] [Field Ω] [Algebra K Ω]
    [IsGalois K Ω]
    (E : IntermediateField K Ω)
    (x : Eˣ)
    (q : (closedFixingSubgroup K Ω
        (⊥ : IntermediateField K Ω)).toSubgroup ⧸
      extensionSubgroup
        (closedFixingSubgroup K Ω (⊥ : IntermediateField K Ω))
        (closedFixingSubgroup K Ω E) (fixingSubgroupLeBase K Ω E)) :
    relativeCosetAction_intermediateFieldUnit_val_of_isSeparableStatement
      K Ω E x q := by
  refine Quotient.inductionOn' q ?_
  intro σ
  rfl

end Langlands.NYLL.LocalClassFieldTheory
