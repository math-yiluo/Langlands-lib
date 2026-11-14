/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)

Adapted by Worker 85, 14 November 2026: extracted, without proofs, the types
of the source instance
LocalClassFieldTheory.baseFixingExtensionQuotient_finite_of_isSeparable
(inventory M165.006) and of the source theorem
LocalClassFieldTheory.relativeCosetAction_intermediateFieldUnit_val_of_isSeparable
(inventory M165.008) as the Prop-valued definitions
Langlands.NYLL.LocalClassFieldTheory.baseFixingExtensionQuotient_finite_of_isSeparableStatement
and
Langlands.NYLL.LocalClassFieldTheory.relativeCosetAction_intermediateFieldUnit_val_of_isSeparableStatement.
The source section variables that each declaration uses are written as
explicit binders, in the source order; the propositions are unchanged. The
instance target is an abbrev, so that a proof can be registered as an
instance. The namespace is prefixed with Langlands.NYLL; the NYLL imports are
replaced by the published modules defining the names used. All other source
declarations are omitted. The retained license and notice are
licenses/NYLL/LICENSE and licenses/NYLL/NOTICE.
-/

import Langlands.NYLL.ClassFieldTheory.LocalClassFieldTheory.Finite.LocalReciprocity.SeparableFixedFieldNorm.Initial.Definitions
import Langlands.NYLL.ClassFieldTheory.LocalClassFieldTheory.Finite.LocalReciprocity.AbsoluteUnitsFixedField.FixedUnitsEquiv.Definitions
import Langlands.NYLL.ClassFieldTheory.AbstractClassFieldTheory.Degree.Norm.Definitions

/-!
# Cosets of the base fixing subgroup as embeddings: finiteness and coset-action targets

Source: Naganori Yamaguchi, ClassFieldTheory, commit
fbd320cd8b1b06487c58227e92eb135794267709,
`Nyll/ClassFieldTheory/LocalClassFieldTheory/Finite/LocalReciprocity/SeparableFixedFieldNorm.lean`,
lines 36–37, 41 and 175–176 (section variables), 154–161 (M165.006) and
178–194 (M165.008).
-/

namespace Langlands.NYLL.LocalClassFieldTheory
open RamificationTheory CyclicCohomology ClassFormation

/-- Target of the source instance
`baseFixingExtensionQuotient_finite_of_isSeparable` (M165.006): for a finite
separable intermediate field `E` of a separably closed Galois extension
`Ω / K`, the space of left cosets of `Gal(Ω / E)` in `Gal(Ω / K)` is
finite. -/
abbrev baseFixingExtensionQuotient_finite_of_isSeparableStatement
    (K Ω : Type) [Field K] [Field Ω] [Algebra K Ω]
    [IsGalois K Ω] [IsSepClosed Ω]
    (E : IntermediateField K Ω)
    [FiniteDimensional K E] [Algebra.IsSeparable K E] : Prop :=
  Finite
    ((closedFixingSubgroup K Ω (⊥ : IntermediateField K Ω)).toSubgroup ⧸
      extensionSubgroup
        (closedFixingSubgroup K Ω (⊥ : IntermediateField K Ω))
        (closedFixingSubgroup K Ω E) (fixingSubgroupLeBase K Ω E))

/-- Target of the source theorem
`relativeCosetAction_intermediateFieldUnit_val_of_isSeparable` (M165.008):
the abstract coset action on an `E`-unit is evaluation under the
corresponding actual `K`-embedding of `E`. -/
def relativeCosetAction_intermediateFieldUnit_val_of_isSeparableStatement
    (K Ω : Type) [Field K] [Field Ω] [Algebra K Ω]
    [IsGalois K Ω]
    (E : IntermediateField K Ω)
    (x : Eˣ)
    (q : (closedFixingSubgroup K Ω
        (⊥ : IntermediateField K Ω)).toSubgroup ⧸
      extensionSubgroup
        (closedFixingSubgroup K Ω (⊥ : IntermediateField K Ω))
        (closedFixingSubgroup K Ω E) (fixingSubgroupLeBase K Ω E)) : Prop :=
  ((Additive.toMul
    (relativeCosetAction (galoisAmbientUnitsRep K Ω)
      (closedFixingSubgroup K Ω (⊥ : IntermediateField K Ω))
      (closedFixingSubgroup K Ω E) (fixingSubgroupLeBase K Ω E)
      (intermediateFieldUnitsEquivGaloisFixed K Ω E
        (Additive.ofMul x)) q) : Ωˣ) : Ω) =
    baseFixingCosetToAlgHom K Ω E q (x : E)

end Langlands.NYLL.LocalClassFieldTheory
