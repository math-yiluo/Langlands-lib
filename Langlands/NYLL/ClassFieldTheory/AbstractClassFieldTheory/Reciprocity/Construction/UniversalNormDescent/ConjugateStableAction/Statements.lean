/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import Langlands.NYLL.ClassFieldTheory.AbstractClassFieldTheory.Reciprocity.Construction.UniversalNormDescent.ConjugateStableAction.Definitions
import Langlands.NYLL.ClassFieldTheory.AbstractClassFieldTheory.Degree.Norm.RelativeNorm.Definitions

/-!
# Targets: the conjugation-stable action and its compatibility with norms

Modified by Worker 5264, 15 November 2026: state the source theorems
M043.006 `conjugateStableAction_coe` and M043.007
`relativeNorm_conjugateStableAction` of
`Nyll/ClassFieldTheory/AbstractClassFieldTheory/Reciprocity/Construction/UniversalNormDescent.lean`
at fbd320cd8b1b06487c58227e92eb135794267709 as Prop-valued Statement
definitions. Prefix the namespace with `Langlands.NYLL`, append `Statement`
to the names, replace the source imports by focused published imports and
the import of the M043.003 definition, keep the source universes, opens,
binders and statements unchanged, and omit the proofs, the `@[simp]`
attribute of M043.006 and the rest of the source file. See the paired
Markdown and `licenses/NYLL/LICENSE` and `licenses/NYLL/NOTICE`.
-/

universe u v

namespace Langlands.NYLL.ClassFormation

open KummerTheory
open CyclicCohomology

noncomputable section

open CategoryTheory
open scoped BigOperators

/-- Target: the conjugation-stable action agrees with its ambient action after
coercion. -/
def conjugateStableAction_coeStatement
    {R : IntegralRepGroupType} [Group R] [TopologicalSpace R] [ContinuousMul R]
    (B : Rep ℤ R) (F : ClosedSubgroup R) (s : R)
    (hF : conjugateClosedSubgroup F s = F)
    (a : ambientFixedAddSubgroup B F) : Prop :=
    ((conjugateStableAction B F s hF a : ambientFixedAddSubgroup B F) : B.V) =
      B.ρ s⁻¹ a.1

/-- Target: relative norm is equivariant for a conjugation stabilizing both
fields in the tower. -/
def relativeNorm_conjugateStableActionStatement
    {R : IntegralRepGroupType} [Group R] [TopologicalSpace R] [ContinuousMul R]
    (B : Rep ℤ R) (F E : ClosedSubgroup R)
    (hEF : E.toSubgroup ≤ F.toSubgroup) (s : R)
    [Finite (F.toSubgroup ⧸ extensionSubgroup F E hEF)]
    (hF : conjugateClosedSubgroup F s = F)
    (hE : conjugateClosedSubgroup E s = E)
    (a : ambientFixedAddSubgroup B E) : Prop :=
    relativeNorm B F E hEF (conjugateStableAction B E s hE a) =
      conjugateStableAction B F s hF (relativeNorm B F E hEF a)

end

end Langlands.NYLL.ClassFormation
