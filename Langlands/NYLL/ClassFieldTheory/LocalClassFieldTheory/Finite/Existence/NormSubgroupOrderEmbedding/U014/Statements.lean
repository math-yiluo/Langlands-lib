/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

/-
Modified by Worker 539, 14 November 2026: extract the complete type of
M300.014 from NormSubgroupOrderEmbedding.lean, lines 417–431, at commit
fbd320cd8b1b06487c58227e92eb135794267709 as a Prop-valued definition with
the suffix Statement. Prefix the namespace with Langlands.NYLL, make the
source section parameters explicit in the declaration, omit the proof and
unrelated declarations, and replace the source imports with the focused
norm-subgroup definition, finite-abelian order and Mathlib local-field class.
See the paired Markdown for the full source map and modification record.
The original LICENSE and NOTICE remain in licenses/NYLL/.
-/

import Langlands.NYLL.ClassFieldTheory.LocalClassFieldTheory.Finite.Existence.NormSubgroupOrderEmbedding.Definitions
import Langlands.NYLL.ClassFieldTheory.AbstractClassFieldTheory.Reciprocity.FiniteAbelianSubextension.Order
import Mathlib.NumberTheory.LocalField.Basic

/-!
# Native finite-abelian norm order reversal: proposition target

This is the exact target of NYLL M300.014 on the represented finite abelian
subextensions and their ordinary norm subgroups.
-/

namespace Langlands.NYLL.LocalClassFieldTheory

/-- The order reversal for finite abelian subextensions, expressed for the actual fixed fields and
their ordinary norm subgroups. -/
def finiteAbelianSubextension_le_iff_normSubgroup_leStatement
    (K : Type) [Field K] [ValuativeRel K] [TopologicalSpace K]
    [IsNonarchimedeanLocalField K]
    (L₁ L₂ : ClassFormation.FiniteAbelianSubextension (intrinsicAbstractBase K)) :
    Prop :=
  L₁ ≤ L₂ ↔
    finiteAbelianNormSubgroup K L₂ ≤
      finiteAbelianNormSubgroup K L₁

end Langlands.NYLL.LocalClassFieldTheory
