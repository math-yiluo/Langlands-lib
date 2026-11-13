/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import Langlands.NYLL.ClassFieldTheory.AbstractClassFieldTheory.Degree.Frobenius.Definitions
import Langlands.NYLL.ClassFieldTheory.AbstractClassFieldTheory.Degree.Fields.FiniteResidue.Definitions
import Langlands.NYLL.GaloisCohomology.ProfiniteIntegers.ProfiniteInteger.U002.Definitions
import Mathlib.GroupTheory.Index

/-!
# Targets for the index of the additive degree image

Modified by Worker 5264: extract the two public theorem signatures M011.002
and M011.003 from the pinned NYLL Frobenius source as Prop-valued Statement
definitions. Prefix the namespace with Langlands.NYLL, append `Statement` to
each name, keep the source variable declaration, parameters and binder kinds,
and omit the proofs and the `@[simp]` attribute. Replace the source import of
the whole Fields module by the published focused modules that supply the
actual degree datum, finite-residue fields, additive image and natural
multiplication on `ℤ̂`.
See the paired Markdown and licenses/NYLL/LICENSE and NOTICE.
-/

namespace Langlands.NYLL.ClassFormation

noncomputable section

variable {G : Type*} [Group G] [TopologicalSpace G]

namespace DegreeData

/-- Target: the additive degree image has index equal to the field's positive
residue degree. -/
def fieldImageAdd_indexStatement (D : DegreeData G)
    (K : FiniteResidueAbstractField D) : Prop :=
  (D.fieldImageAdd K.field).index = (K.residueDegree : ℕ)

/-- Target: finite residue degree identifies `d(G_K)` with `f_K ℤ̂`. -/
def fieldImageAdd_eq_mulNat_rangeStatement (D : DegreeData G)
    (K : FiniteResidueAbstractField D) : Prop :=
  D.fieldImageAdd K.field =
    (zHatMulNat (K.residueDegree : ℕ)).toAddMonoidHom.range

end DegreeData

end
end Langlands.NYLL.ClassFormation
