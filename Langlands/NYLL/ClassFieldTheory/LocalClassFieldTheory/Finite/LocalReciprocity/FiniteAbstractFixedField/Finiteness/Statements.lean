/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import Langlands.NYLL.ClassFieldTheory.AbstractClassFieldTheory.Degree.Fields.U005.Proofs
import Langlands.NYLL.GaloisCohomology.Cyclic.NormKernelVanishing.Extension.Definitions
import Langlands.NYLL.ClassFieldTheory.LocalClassFieldTheory.Finite.LocalReciprocity.FiniteAbstractFixedField.Initial.Definitions

/-!
# Finite abstract fields inside a Galois ambient field: finiteness targets

Adapted by Worker 90 from NYLL commit
`fbd320cd8b1b06487c58227e92eb135794267709`,
`Nyll/ClassFieldTheory/LocalClassFieldTheory/Finite/LocalReciprocity/FiniteAbstractFixedField.lean`,
lines 48–90 (M099.003–M099.005).

Modifications by Worker 90: the three source theorems become Prop-valued
`Statement` definitions whose bodies are the source conclusions; prefix the
namespace `LocalClassFieldTheory` with `Langlands.NYLL`; write the source
section variables as explicit binders in the source order, keeping the
`omit [IsGalois k Ω]` of the first two targets and the `IsGalois` instance of
the third; replace the source imports by the published modules providing
`baseField`, `le_baseField`, `extensionSubgroup` and `abstractFixedField`;
omit the proofs and the source `open` lines; silence the unused-variable
linter for the hypothesis `hfinite`, which the conclusions do not mention.
See the paired Markdown and `licenses/NYLL/LICENSE` and
`licenses/NYLL/NOTICE`.
-/

namespace Langlands.NYLL.LocalClassFieldTheory

open CyclicCohomology ClassFormation

set_option linter.unusedVariables false in
/-- Target for M099.003: absolute finiteness in the abstract class-formation
quotient presentation gives a finite quotient of the ambient absolute Galois
group by the same subgroup. As in the source (`omit [IsGalois k Ω] in`),
there is no Galois hypothesis. -/
def ambientQuotientFiniteOfAbstractFiniteStatement
    (k Ω : Type) [Field k] [Field Ω] [Algebra k Ω]
    (H : ClosedSubgroup (Gal(Ω/k)))
    (hfinite : Finite ((baseField (Gal(Ω/k))).toSubgroup ⧸
      extensionSubgroup (baseField (Gal(Ω/k))) H (le_baseField H))) : Prop :=
  Finite (Gal(Ω/k) ⧸ H.toSubgroup)

set_option linter.unusedVariables false in
/-- Target for M099.004: an abstract field finite over the distinguished base
is represented by an open subgroup of the absolute Galois group. As in the
source (`omit [IsGalois k Ω] in`), there is no Galois hypothesis. -/
def abstractFiniteClosedSubgroup_isOpenStatement
    (k Ω : Type) [Field k] [Field Ω] [Algebra k Ω]
    (H : ClosedSubgroup (Gal(Ω/k)))
    (hfinite : Finite ((baseField (Gal(Ω/k))).toSubgroup ⧸
      extensionSubgroup (baseField (Gal(Ω/k))) H (le_baseField H))) : Prop :=
  IsOpen H.carrier

set_option linter.unusedVariables false in
/-- Target for M099.005: the fixed field of an abstract field finite over the
distinguished base is an actual finite field extension. The source theorem
keeps the section's `IsGalois k Ω` instance, so this target keeps it too. -/
def abstractFixedField_finiteDimensionalStatement
    (k Ω : Type) [Field k] [Field Ω] [Algebra k Ω] [IsGalois k Ω]
    (H : ClosedSubgroup (Gal(Ω/k)))
    (hfinite : Finite ((baseField (Gal(Ω/k))).toSubgroup ⧸
      extensionSubgroup (baseField (Gal(Ω/k))) H (le_baseField H))) : Prop :=
  FiniteDimensional k (abstractFixedField k Ω H)

end Langlands.NYLL.LocalClassFieldTheory
