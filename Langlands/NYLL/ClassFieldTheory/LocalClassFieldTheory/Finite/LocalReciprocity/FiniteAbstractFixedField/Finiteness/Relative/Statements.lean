/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import Langlands.NYLL.ClassFieldTheory.AbstractClassFieldTheory.Degree.Fields.U005.Proofs
import Langlands.NYLL.GaloisCohomology.Cyclic.NormKernelVanishing.Extension.Definitions
import Langlands.NYLL.ClassFieldTheory.LocalClassFieldTheory.Finite.LocalReciprocity.FiniteAbstractFixedField.Initial.Definitions
import Langlands.NYLL.ClassFieldTheory.LocalClassFieldTheory.Finite.LocalReciprocity.FiniteAbstractFixedField.Initial.U006.Proofs

/-!
# Finite abstract fields inside a Galois ambient field: relative finiteness target

Adapted by Worker 90 from NYLL commit
`fbd320cd8b1b06487c58227e92eb135794267709`,
`Nyll/ClassFieldTheory/LocalClassFieldTheory/Finite/LocalReciprocity/FiniteAbstractFixedField.lean`,
lines 304–317 (M099.018).

Modifications by Worker 90: the source theorem becomes a Prop-valued
`Statement` definition whose body is the source conclusion, including its
`letI` algebra binder built from the published proof `abstractFixedField_le`
(M099.006); prefix the namespace `LocalClassFieldTheory` with
`Langlands.NYLL`; write the source section variables as explicit binders in
the source order, keeping the section's `IsGalois k Ω` instance; replace the
source imports by the published modules providing `baseField`,
`le_baseField`, `extensionSubgroup`, `abstractFixedField` and
`abstractFixedField_le`; omit the proof and the source `open` lines; silence
the unused-variable linter for the hypotheses `hKfinite` and `hLKfinite`,
which the conclusion does not mention. See the paired Markdown and
`licenses/NYLL/LICENSE` and `licenses/NYLL/NOTICE`.
-/

namespace Langlands.NYLL.LocalClassFieldTheory

open CyclicCohomology ClassFormation

set_option linter.unusedVariables false in
/-- Target for M099.018: in a finite abstract tower `L / K / k`, the concrete
upper fixed field is finite over the concrete lower fixed field. The source
theorem keeps the section's `IsGalois k Ω` instance, so this target keeps it
too. -/
def abstractFixedField_relativeFiniteDimensionalStatement
    (k Ω : Type) [Field k] [Field Ω] [Algebra k Ω] [IsGalois k Ω]
    (K L : ClosedSubgroup (Gal(Ω/k)))
    (hLK : L.toSubgroup ≤ K.toSubgroup)
    (hKfinite : Finite ((baseField (Gal(Ω/k))).toSubgroup ⧸
      extensionSubgroup (baseField (Gal(Ω/k))) K (le_baseField K)))
    (hLKfinite : Finite
      (K.toSubgroup ⧸ extensionSubgroup K L hLK)) : Prop :=
  letI : Algebra (abstractFixedField k Ω K) (abstractFixedField k Ω L) :=
    RingHom.toAlgebra
      (IntermediateField.inclusion (abstractFixedField_le k Ω hLK))
  FiniteDimensional (abstractFixedField k Ω K)
    (abstractFixedField k Ω L)

end Langlands.NYLL.LocalClassFieldTheory
