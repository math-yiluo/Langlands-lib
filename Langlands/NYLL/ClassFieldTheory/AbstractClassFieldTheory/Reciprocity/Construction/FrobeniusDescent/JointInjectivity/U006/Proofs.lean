/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
Modifications by Worker 747 (2026-11-16): extract this focused M017.006 proof
from the pinned source at fbd320cd8b1b06487c58227e92eb135794267709;
prefix its namespace by Langlands.NYLL, import its published Prop target,
and prove that exact target. Proof adaptations and dependencies are recorded
in the paired Markdown. Retained license and notices:
licenses/NYLL/LICENSE and licenses/NYLL/NOTICE.
-/

import Langlands.NYLL.ClassFieldTheory.AbstractClassFieldTheory.Reciprocity.Construction.FrobeniusDescent.JointInjectivity.Statements

namespace Langlands.NYLL.ClassFormation

open CyclicCohomology

noncomputable section

variable {G : Type*} [Group G] [TopologicalSpace G]

namespace DegreeData

/-- Proof of NYLL M017.006, with the exact published target: restriction of
Frobenius elements is multiplicative. -/
theorem frobeniusRestriction_mul (D : DegreeData G)
    (K : FiniteResidueAbstractField D) (L : ClosedSubgroup G)
    (hLK : L.toSubgroup ≤ K.field.toSubgroup)
    [hLnormal : (extensionSubgroup K.field L hLK).Normal]
    (σ τ : D.FrobeniusElements K L hLK) :
    frobeniusRestriction_mulStatement D K L hLK σ τ := by
  unfold frobeniusRestriction_mulStatement
  change D.extensionRestriction K.field L hLK (σ.1 * τ.1) =
    D.extensionRestriction K.field L hLK σ.1 *
      D.extensionRestriction K.field L hLK τ.1
  exact map_mul _ _ _

end DegreeData

end

end Langlands.NYLL.ClassFormation
