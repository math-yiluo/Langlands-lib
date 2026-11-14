/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import Langlands.NYLL.ClassFieldTheory.AbstractClassFieldTheory.Reciprocity.FiniteAbelianSubextension.Definitions
import Langlands.NYLL.ClassFieldTheory.AbstractClassFieldTheory.Degree.Fields.U005.Proofs
import Langlands.NYLL.ClassFieldTheory.LocalClassFieldTheory.Finite.LocalReciprocity.IntrinsicAbsoluteData.Initial.Definitions

/-!
# Finite abelian subextensions over the absolute base: proposition targets

Modified by Worker 451, 14 November 2026: extract the types of M300.001 and
M300.002 (lines 36–40 and 50–53) of the pinned NYLL
`Nyll/ClassFieldTheory/LocalClassFieldTheory/Finite/Existence/NormSubgroupOrderEmbedding.lean`
at `fbd320cd8b1b06487c58227e92eb135794267709`. Each source theorem becomes a
Prop-valued definition with the suffix `Statement`; the source section
variables `(K : Type) [Field K]` are written as the leading explicit binders
of each definition, and the proofs are omitted. The namespace is prefixed with
`Langlands.NYLL`, the source imports are replaced by the published modules
supplying the used declarations, and the unused openings `LocalFieldTheory`,
`RamificationTheory` and `KummerTheory` are dropped. See the paired Markdown
for the declaration map and complete modification record. The original
license and notices are retained in `licenses/NYLL/LICENSE` and
`licenses/NYLL/NOTICE`.
-/

noncomputable section

namespace Langlands.NYLL.LocalClassFieldTheory

open CyclicCohomology
open ClassFormation

/-- Finiteness over the concrete ground-field fixing group implies
finiteness over the abstract class-formation `baseField`. -/
def finiteAbelianSubextension_finite_over_absoluteBaseStatement
    (K : Type) [Field K]
    (L : FiniteAbelianSubextension (intrinsicAbstractBase K)) : Prop :=
  Finite ((baseField (intrinsicAbsoluteGalois K)).toSubgroup ⧸
    extensionSubgroup (baseField (intrinsicAbsoluteGalois K)) L.field
      (le_baseField L.field))

/-- Normality over the concrete ground-field fixing group is normality over
the abstract class-formation `baseField`. -/
def finiteAbelianSubextension_normal_over_absoluteBaseStatement
    (K : Type) [Field K]
    (L : FiniteAbelianSubextension (intrinsicAbstractBase K)) : Prop :=
  (extensionSubgroup (baseField (intrinsicAbsoluteGalois K)) L.field
    (le_baseField L.field)).Normal

end Langlands.NYLL.LocalClassFieldTheory
