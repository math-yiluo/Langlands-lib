/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

/-
Modifications by Worker 85, 15 November 2026:
Extract the statement of M249.021 (localSeparableResidueAlgAction_surjective,
lines 393–395) from
Nyll/ClassFieldTheory/LocalClassFieldTheory/Finite/LocalReciprocity/
LocalResidueDatum.lean
at fbd320cd8b1b06487c58227e92eb135794267709 as a closed Prop-valued
definition without its proof. The section variable K and its instance
binders (lines 45–46) become leading universal binders. Add the
Langlands.NYLL namespace prefix and the suffix Statement. Import the Library
module that publishes localSeparableResidueAlgAction instead of the source
imports. Omit the noncomputable section, the open lines and local instances
this statement does not need, and all other declarations.
The original LICENSE and NOTICE are retained in licenses/NYLL/.
-/

import Langlands.NYLL.ClassFieldTheory.LocalClassFieldTheory.Finite.LocalReciprocity.LocalResidueDatum.U020.Definitions

/-!
# Surjectivity of the continuous local residue action

A closed proposition: for a nonarchimedean local field `K`, the continuous
residue action `localSeparableResidueAlgAction K` of the absolute Galois
group `Gal(SeparableClosure K / K)` on the selected residue field is
surjective.
-/

namespace Langlands.NYLL.LocalClassFieldTheory

/-- States the theorem `localSeparableResidueAlgAction_surjective`: every
automorphism of the selected residue extension lifts to the separable Galois
group. -/
def localSeparableResidueAlgAction_surjectiveStatement : Prop :=
  ∀ (K : Type) [Field K] [ValuativeRel K] [TopologicalSpace K]
    [IsNonarchimedeanLocalField K],
    Function.Surjective (localSeparableResidueAlgAction K)

end Langlands.NYLL.LocalClassFieldTheory
