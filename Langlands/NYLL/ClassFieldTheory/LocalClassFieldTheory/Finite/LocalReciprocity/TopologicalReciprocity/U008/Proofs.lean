/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

/-
Modifications by Worker 66, 13 November 2026: extract the proof of M257.008
(`normQuotient_discrete`) from
Nyll/ClassFieldTheory/LocalClassFieldTheory/Finite/LocalReciprocity/
TopologicalReciprocity.lean at fbd320cd8b1b06487c58227e92eb135794267709.
Prefix the namespace with Langlands.NYLL, state the conclusion as the
published normQuotient_discreteStatement K L, restore the published M257.001
topology instance d001 locally, and import only the published U006 target and
the published U007 openness proof. Retain all Type-zero parameters, their
order and the first three lines of the original proof; close the last
goal with `exact` because the published openness theorem's type is its
Statement, which `simpa only [N]` does not unfold.
LICENSE and NOTICE are retained in licenses/NYLL/.
-/

import Langlands.NYLL.ClassFieldTheory.LocalClassFieldTheory.Finite.LocalReciprocity.TopologicalReciprocity.U006.Statements
import Langlands.NYLL.ClassFieldTheory.LocalClassFieldTheory.Finite.LocalReciprocity.TopologicalReciprocity.U007.Proofs

/-! # Discreteness of the native norm quotient (M257.008) -/

open Langlands.NYLL.LocalFieldTheory

attribute [local instance] Langlands.NYLL.PortInternal.M257.d001

namespace Langlands.NYLL.LocalClassFieldTheory

/-- The native quotient topology on the finite norm quotient is discrete. -/
theorem normQuotient_discrete
    (K L : Type) [Field K] [Field L] [Algebra K L]
    [FiniteDimensional K L] [IsGalois K L]
    [ValuativeRel K] [TopologicalSpace K]
    [IsNonarchimedeanLocalField K] :
    normQuotient_discreteStatement K L := by
  let N := localNormSubgroup K L
  change DiscreteTopology (Kˣ ⧸ N)
  apply QuotientGroup.discreteTopology
  exact localNormSubgroup_isOpen K L

end Langlands.NYLL.LocalClassFieldTheory
