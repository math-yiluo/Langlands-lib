/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)

Adapted by Worker 85, 13 November 2026: extracted the statements of the
private source theorems LocalClassFieldTheory.baseFixingCosetToAlgHom_surjective
(inventory M165.003) and LocalClassFieldTheory.baseFixingCosetToAlgHom_injective
(inventory M165.004) as the Prop-valued definitions
Langlands.NYLL.PortInternal.M165.d003Statement and
Langlands.NYLL.PortInternal.M165.d004Statement, the names reserved by the
port plan. The source section variables that each theorem uses are written as
explicit binders of the definition, in the source order; the propositions are
unchanged. Proofs are omitted. The NYLL imports are replaced by the module
defining baseFixingCosetToAlgHom. The retained license and notice are
licenses/NYLL/LICENSE and licenses/NYLL/NOTICE.
-/

import Langlands.NYLL.ClassFieldTheory.LocalClassFieldTheory.Finite.LocalReciprocity.SeparableFixedFieldNorm.Initial.Definitions

/-!
# Cosets of the base fixing subgroup as embeddings: surjectivity and injectivity targets

Source: Naganori Yamaguchi, ClassFieldTheory, commit
fbd320cd8b1b06487c58227e92eb135794267709,
`Nyll/ClassFieldTheory/LocalClassFieldTheory/Finite/LocalReciprocity/SeparableFixedFieldNorm.lean`,
lines 36–37 and 41 (section variables), 91–93 (M165.003) and 119–121 (M165.004).
-/

namespace Langlands.NYLL.LocalClassFieldTheory

noncomputable section

/-- Statement target for the private source theorem
`baseFixingCosetToAlgHom_surjective` (M165.003): for a finite separable
intermediate field `E` of a separably closed Galois extension `Ω / K`, every
`K`-embedding of `E` into `Ω` is the restriction of an element of
`Gal(Ω / K)`. -/
def _root_.Langlands.NYLL.PortInternal.M165.d003Statement
    (K Ω : Type) [Field K] [Field Ω] [Algebra K Ω]
    [IsGalois K Ω] [IsSepClosed Ω]
    (E : IntermediateField K Ω)
    [FiniteDimensional K E] [Algebra.IsSeparable K E] : Prop :=
  Function.Surjective (baseFixingCosetToAlgHom K Ω E)

/-- Statement target for the private source theorem
`baseFixingCosetToAlgHom_injective` (M165.004): two left cosets of
`Gal(Ω / E)` with the same restriction to `E` are equal. -/
def _root_.Langlands.NYLL.PortInternal.M165.d004Statement
    (K Ω : Type) [Field K] [Field Ω] [Algebra K Ω]
    [IsGalois K Ω]
    (E : IntermediateField K Ω) : Prop :=
  Function.Injective (baseFixingCosetToAlgHom K Ω E)

end
end Langlands.NYLL.LocalClassFieldTheory
