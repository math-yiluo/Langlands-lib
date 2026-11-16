/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
Modifications by Worker 747 (2026-11-16): extract this focused M017.007 proof
from the pinned source at fbd320cd8b1b06487c58227e92eb135794267709;
prefix its namespace by Langlands.NYLL, import its published Prop target,
and prove that exact target. Proof adaptations and dependencies are recorded
in the paired Markdown. Retained license and notices:
licenses/NYLL/LICENSE and licenses/NYLL/NOTICE.
-/

import Langlands.NYLL.ClassFieldTheory.AbstractClassFieldTheory.Degree.Frobenius.NormalizedDegree.U010.Proofs
import Langlands.NYLL.ClassFieldTheory.AbstractClassFieldTheory.Reciprocity.Construction.FrobeniusDescent.JointInjectivity.Statements

namespace Langlands.NYLL.ClassFormation

open CyclicCohomology

noncomputable section

variable {G : Type*} [Group G] [TopologicalSpace G]

namespace DegreeData

/-- Local private copy of the M017.005 argument (the published theorem
`extensionRestriction_normalizedDegree_joint_injective` is not yet in the
Library at this workspace base): restriction and normalized degree jointly
distinguish elements of `G(\widetilde L/K)`. -/
private theorem extensionRestriction_normalizedDegree_joint_injective_local
    (D : DegreeData G) (K : FiniteResidueAbstractField D)
    (L : ClosedSubgroup G)
    (hLK : L.toSubgroup ≤ K.field.toSubgroup)
    [hLnormal : (extensionSubgroup K.field L hLK).Normal] :
    Function.Injective (fun q :
        K.field.toSubgroup ⧸ D.extensionInertiaWithin K.field L hLK =>
      (D.extensionRestriction K.field L hLK q,
        D.extensionNormalizedDegree K L hLK q)) := by
  intro q r hqr
  refine Quotient.inductionOn₂' q r ?_ hqr
  intro a b hab
  apply QuotientGroup.eq.mpr
  have hRestriction : QuotientGroup.mk a =
      (QuotientGroup.mk b :
        K.field.toSubgroup ⧸ extensionSubgroup K.field L hLK) := by
    exact congrArg Prod.fst hab
  have hExtension : a⁻¹ * b ∈ extensionSubgroup K.field L hLK :=
    QuotientGroup.eq.mp hRestriction
  have hDegree : D.normalizedDegree K a =
      D.normalizedDegree K b :=
    congrArg Prod.snd hab
  refine ⟨hExtension, ?_⟩
  have hker : (D.normalizedDegree K).toMonoidHom.ker =
      D.fieldInertiaWithin K.field :=
    D.normalizedDegree_ker K
  rw [← hker]
  change D.normalizedDegree K (a⁻¹ * b) = 1
  rw [map_mul, map_inv, hDegree, inv_mul_cancel]

/-- Proof of NYLL M017.007, with the exact published target: Frobenius
elements with equal restriction and equal normalized degree are equal. -/
theorem frobenius_eq_of_restriction_eq_of_degree_eq
    (D : DegreeData G) (K : FiniteResidueAbstractField D)
    (L : ClosedSubgroup G)
    (hLK : L.toSubgroup ≤ K.field.toSubgroup)
    [hLnormal : (extensionSubgroup K.field L hLK).Normal]
    {σ τ : D.FrobeniusElements K L hLK}
    (hRestriction :
      D.frobeniusRestriction K L hLK σ =
        D.frobeniusRestriction K L hLK τ)
    (hDegree :
      D.extensionNormalizedDegree K L hLK σ.1 =
        D.extensionNormalizedDegree K L hLK τ.1) :
    frobenius_eq_of_restriction_eq_of_degree_eqStatement D K L hLK
      hRestriction hDegree := by
  unfold frobenius_eq_of_restriction_eq_of_degree_eqStatement
  apply Subtype.ext
  apply D.extensionRestriction_normalizedDegree_joint_injective_local
    K L hLK
  exact Prod.ext hRestriction hDegree

end DegreeData

end

end Langlands.NYLL.ClassFormation
