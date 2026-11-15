/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)

Adapted by Worker 85, 15 November 2026: extracted, without its proof, the
type of the source theorem
LocalClassFieldTheory.relativeNorm_intermediateFieldUnit_val_of_isSeparable
(inventory M165.009) as the Prop-valued definition
Langlands.NYLL.LocalClassFieldTheory.relativeNorm_intermediateFieldUnit_val_of_isSeparableStatement.
The source section variables are written as explicit binders, in the source
order; the proposition is unchanged. The `Finite` instance that the source
`relativeNorm` uses is the published M165.006 instance
Langlands.NYLL.LocalClassFieldTheory.baseFixingExtensionQuotient_finite_of_isSeparable,
found by instance search as in the source. The namespace is prefixed with
Langlands.NYLL; the NYLL imports are replaced by the published modules
defining the names used. All other source declarations are omitted. The
retained license and notice are licenses/NYLL/LICENSE and
licenses/NYLL/NOTICE.
-/

import Langlands.NYLL.ClassFieldTheory.LocalClassFieldTheory.Finite.LocalReciprocity.SeparableFixedFieldNorm.U006.Proofs
import Langlands.NYLL.ClassFieldTheory.LocalClassFieldTheory.Finite.LocalReciprocity.AbsoluteUnitsFixedField.FixedUnitsEquiv.Definitions
import Langlands.NYLL.ClassFieldTheory.AbstractClassFieldTheory.Degree.Norm.RelativeNorm.Definitions

/-!
# Norms from a finite separable intermediate field: target

Source: Naganori Yamaguchi, ClassFieldTheory, commit
fbd320cd8b1b06487c58227e92eb135794267709,
`Nyll/ClassFieldTheory/LocalClassFieldTheory/Finite/LocalReciprocity/SeparableFixedFieldNorm.lean`,
lines 36–37 and 175–176 (section variables) and 199–208 (M165.009).
-/

namespace Langlands.NYLL.LocalClassFieldTheory
open RamificationTheory CyclicCohomology ClassFormation

/-- Target of the source theorem
`relativeNorm_intermediateFieldUnit_val_of_isSeparable` (M165.009): for
every finite separable intermediate field `E`, including a nonnormal one, the
abstract class-formation left-coset norm of an `E`-unit `x`, viewed in `Ω`,
is the image in `Ω` of the field norm of `x` from `E` to `K`. -/
def relativeNorm_intermediateFieldUnit_val_of_isSeparableStatement
    (K Ω : Type) [Field K] [Field Ω] [Algebra K Ω]
    [IsGalois K Ω] [IsSepClosed Ω]
    (E : IntermediateField K Ω)
    [FiniteDimensional K E] [Algebra.IsSeparable K E]
    (x : Eˣ) : Prop :=
  ((Additive.toMul
    ((relativeNorm (galoisAmbientUnitsRep K Ω)
      (closedFixingSubgroup K Ω (⊥ : IntermediateField K Ω))
      (closedFixingSubgroup K Ω E) (fixingSubgroupLeBase K Ω E)
      (intermediateFieldUnitsEquivGaloisFixed K Ω E
        (Additive.ofMul x))).1 : Additive Ωˣ) : Ωˣ) : Ω) =
    algebraMap K Ω (Algebra.norm K (x : E))

end Langlands.NYLL.LocalClassFieldTheory
