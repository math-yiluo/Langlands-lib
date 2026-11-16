/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import Langlands.NYLL.ClassFieldTheory.AbstractClassFieldTheory.Reciprocity.Construction.FrobeniusPowerFixedField.DegreeZeroCommutes.Statements
import Langlands.NYLL.ClassFieldTheory.AbstractClassFieldTheory.Degree.Frobenius.NormalizedDegree.U010.Proofs

/-!
# NYLL M038.001: inertia commutes with elements fixing the extension

Modified by Worker 5264, 15 November 2026: prove the published target
`DegreeData.extensionInertia_commutes_of_mem_extensionSubgroupStatement`
(M038.001) by the source proof of
`DegreeData.extensionInertia_commutes_of_mem_extensionSubgroup` in
`Nyll/ClassFieldTheory/AbstractClassFieldTheory/Reciprocity/Construction/FrobeniusPowerFixedField.lean`
at fbd320cd8b1b06487c58227e92eb135794267709. Prefix the namespace with
`Langlands.NYLL`, give the theorem the published proposition as its type,
begin the proof with `show` stating it unfolded, and rewrite with the local
fact `hker`, the published `...Statement`-typed M011.010
`normalizedDegree_ker` stated unfolded, in place of the source
`rw [← D.normalizedDegree_ker K]`. The source closes the second membership
goal with `simp [mul_assoc]`, which does not close it with the published
simp set; the port closes it with
`simpa [mul_assoc] using (D.fieldInertiaWithin K.field).mul_mem
((D.fieldInertiaWithin K.field).inv_mem htI) hconj`, the product of `t⁻¹`
and the conjugate `hconj` already proved in the source step. Replace the
source import by published modules and omit the unused opens and the rest of
the source file. See the paired Markdown and `licenses/NYLL/LICENSE` and
`licenses/NYLL/NOTICE`.
-/

universe u

namespace Langlands.NYLL.ClassFormation

open CyclicCohomology

noncomputable section

section degreeOnePowerFields

variable {G : Type u} [Group G] [TopologicalSpace G]

namespace DegreeData

/-- An element fixing `L` commutes modulo `G_{\widetilde L}` with every
degree-zero element of `G(\widetilde L/K)`.  Group-theoretically this is
`[G_L,I_K] ⊆ G_L ∩ I_K = G_{\widetilde L}`; it is the reason the
fields fixed by the powers of `φⁿ` in the universal norm-descent lemma are stable under the
elements `τᵢ` occurring in `(*)`. -/
theorem extensionInertia_commutes_of_mem_extensionSubgroup (D : DegreeData G)
    (K : FiniteResidueAbstractField D) (L : ClosedSubgroup G)
    (hLK : L.toSubgroup ≤ K.field.toSubgroup)
    [hLnormal : (extensionSubgroup K.field L hLK).Normal]
    (k : K.field.toSubgroup) (hk : k ∈ extensionSubgroup K.field L hLK)
    (q : K.field.toSubgroup ⧸ D.extensionInertiaWithin K.field L hLK)
    (hq : D.extensionNormalizedDegree K L hLK q = 1) :
    extensionInertia_commutes_of_mem_extensionSubgroupStatement D K L hLK k hk q hq := by
  show (QuotientGroup.mk k :
      K.field.toSubgroup ⧸ D.extensionInertiaWithin K.field L hLK) * q =
    q * QuotientGroup.mk k
  have hker : (D.normalizedDegree K).toMonoidHom.ker = D.fieldInertiaWithin K.field :=
    D.normalizedDegree_ker K
  revert hq
  refine Quotient.inductionOn' q ?_
  intro t hdt
  have htI : t ∈ D.fieldInertiaWithin K.field := by
    rw [← hker]
    exact hdt
  change QuotientGroup.mk (k * t) = QuotientGroup.mk (t * k)
  apply QuotientGroup.eq.mpr
  constructor
  · change (k * t)⁻¹ * (t * k) ∈ extensionSubgroup K.field L hLK
    have hconj : t⁻¹ * k⁻¹ * t ∈ extensionSubgroup K.field L hLK := by
      simpa using hLnormal.conj_mem k⁻¹
        ((extensionSubgroup K.field L hLK).inv_mem hk) t⁻¹
    simpa [mul_assoc] using
      (extensionSubgroup K.field L hLK).mul_mem hconj hk
  · change (k * t)⁻¹ * (t * k) ∈ D.fieldInertiaWithin K.field
    have hconj : k⁻¹ * t * k ∈ D.fieldInertiaWithin K.field := by
      simpa using (inferInstance : (D.fieldInertiaWithin K.field).Normal).conj_mem
        t htI k⁻¹
    simpa [mul_assoc] using
      (D.fieldInertiaWithin K.field).mul_mem
        ((D.fieldInertiaWithin K.field).inv_mem htI) hconj

end DegreeData

end degreeOnePowerFields

end

end Langlands.NYLL.ClassFormation
