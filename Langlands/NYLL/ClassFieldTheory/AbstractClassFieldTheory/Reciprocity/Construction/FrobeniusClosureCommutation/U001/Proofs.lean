/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import Langlands.NYLL.ClassFieldTheory.AbstractClassFieldTheory.Reciprocity.Construction.FrobeniusClosureCommutation.Statements

/-!
# Commuting with a Frobenius lift means commuting with its closure

Modified by Worker 5264, 15 November 2026: prove the published target
`frobeniusClosure_commutes_of_commutes_generatorStatement` (M042.001) by the
source proof of `frobeniusClosure_commutes_of_commutes_generator` in
`Nyll/ClassFieldTheory/AbstractClassFieldTheory/Reciprocity/Construction/FrobeniusClosureCommutation.lean`
at fbd320cd8b1b06487c58227e92eb135794267709. Prefix the namespace with
`Langlands.NYLL`, give the theorem the published proposition as its type,
unfolded by an initial `show`, and replace the source application of the
unpublished theorem `extensionInertiaWithin_isClosed` (M014.022) by its source
proof, inlined as the local instance. See the paired Markdown and
`licenses/NYLL/LICENSE` and `licenses/NYLL/NOTICE`.
-/

universe u

namespace Langlands.NYLL.ClassFormation

noncomputable section

section frobeniusClosureCommutation

variable {G : Type u} [Group G] [TopologicalSpace G]

namespace DegreeData

/-- Commuting with the chosen generator means commuting with its closed
procyclic closure. -/
theorem frobeniusClosure_commutes_of_commutes_generator (D : DegreeData G)
    [IsTopologicalGroup G] [CompactSpace G] [T2Space G]
    [TotallyDisconnectedSpace G]
    (K : FiniteResidueAbstractField D) (L : ClosedSubgroup G)
    (hLK : L.toSubgroup ≤ K.field.toSubgroup)
    [hLnormal : (L.toSubgroup.subgroupOf K.field.toSubgroup).Normal]
    (σ : D.FrobeniusElements K L hLK)
    (q : K.field.toSubgroup ⧸ D.extensionInertiaWithin K.field L hLK)
    (hq : q * σ.1 = σ.1 * q)
    (c : D.frobeniusClosure K L hLK σ) :
    frobeniusClosure_commutes_of_commutes_generatorStatement D K L hLK σ q hq c := by
  show q * c.1 = c.1 * q
  let : IsClosed
      (D.extensionInertiaWithin K.field L hLK : Set K.field.toSubgroup) := by
    have hE : IsClosed
        (L.toSubgroup.subgroupOf K.field.toSubgroup : Set K.field.toSubgroup) := by
      change IsClosed ((fun x : K.field.toSubgroup => (x : G)) ⁻¹' (L : Set G))
      exact L.isClosed'.preimage continuous_subtype_val
    have hI : IsClosed (D.fieldInertiaWithin K.field : Set K.field.toSubgroup) := by
      let : T2Space ZHatMul := by
        change T2Space ZHat
        infer_instance
      change IsClosed {x : K.field.toSubgroup | D.degree x.1 = 1}
      exact isClosed_eq
        (D.restrictedDegree K.field).continuous_toFun continuous_const
    change IsClosed
      ((L.toSubgroup.subgroupOf K.field.toSubgroup ⊓ D.fieldInertiaWithin K.field) :
        Set K.field.toSubgroup)
    exact hE.inter hI
  let : T2Space
      (K.field.toSubgroup ⧸ D.extensionInertiaWithin K.field L hLK) := by
    infer_instance
  let Q := K.field.toSubgroup ⧸ D.extensionInertiaWithin K.field L hLK
  let X : Set Q := Set.range (fun _ : Unit => σ.1)
  have hclosure : Subgroup.closure X ≤
      Subgroup.centralizer ({q} : Set Q) := by
    rw [Subgroup.closure_le]
    rintro x ⟨i, rfl⟩
    exact Subgroup.mem_centralizer_singleton_iff.mpr hq.symm
  have htop : (Subgroup.closure X).topologicalClosure ≤
      Subgroup.centralizer ({q} : Set Q) :=
    Subgroup.topologicalClosure_minimal _ hclosure
      (Set.isClosed_centralizer (M := Q) ({q} : Set Q))
  have hc : c.1 ∈ (Subgroup.closure X).topologicalClosure := c.2
  exact (Subgroup.mem_centralizer_singleton_iff.mp (htop hc)).symm

end DegreeData

end frobeniusClosureCommutation

end

end Langlands.NYLL.ClassFormation
