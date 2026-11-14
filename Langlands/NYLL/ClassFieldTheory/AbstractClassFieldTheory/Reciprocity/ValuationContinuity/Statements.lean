/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import Langlands.NYLL.ClassFieldTheory.AbstractClassFieldTheory.Reciprocity.ValuationContinuity.Definitions

/-!
# Targets for the unramified degree homomorphism and its kernel

Modified by Worker 114: extract M301.003, M301.004 and M301.009 from the
pinned NYLL ValuationContinuity source, prefix the namespace with
Langlands.NYLL, and convert each source theorem to a Prop-valued
`...Statement` definition with the same telescope and proposition; the
source proofs are omitted. See the paired Markdown and
licenses/NYLL/LICENSE and NOTICE.
-/

noncomputable section

namespace Langlands.NYLL.ClassFormation

universe u

section DegreeOnly

variable {G : Type u} [Group G] [TopologicalSpace G]

namespace DegreeData

/-- The defining kernel equation for the reduction subgroup. -/
def unramifiedDegreeKernelWithin_eq_kerStatement (D : DegreeData G)
    (K : FiniteResidueAbstractField D) (f : ℕ) (hf : 0 < f) : Prop :=
  unramifiedDegreeKernelWithin D K f hf =
    (unramifiedDegreeHom D K f hf).toMonoidHom.ker

/--
The kernel of normalized degree modulo a positive integer is closed inside the finite-residue
field subgroup.
-/
def unramifiedDegreeKernelWithin_isClosedStatement (D : DegreeData G)
    (K : FiniteResidueAbstractField D)
    (f : ℕ) (hf : 0 < f) : Prop :=
  IsClosed (unramifiedDegreeKernelWithin D K f hf :
    Set K.toSubgroup)

/-- The specified map is surjective: `Function.Surjective (unramifiedDegreeHom D K f hf)`. -/
def unramifiedDegreeHom_surjectiveStatement (D : DegreeData G)
    (K : FiniteResidueAbstractField D)
    (f : ℕ) (hf : 0 < f) : Prop :=
  Function.Surjective (unramifiedDegreeHom D K f hf)

end DegreeData

end DegreeOnly

end Langlands.NYLL.ClassFormation
