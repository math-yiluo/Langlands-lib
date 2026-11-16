/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import Langlands.NYLL.ClassFieldTheory.AbstractClassFieldTheory.Reciprocity.CyclicNormQuotient.RelativeNorm.Statements
import Langlands.NYLL.ClassFieldTheory.AbstractClassFieldTheory.Reciprocity.FieldRepresentation.Norm.Statements
import Langlands.NYLL.ClassFieldTheory.AbstractClassFieldTheory.Reciprocity.FieldRepresentation.Action.U004.Proofs

/-!
# NYLL M074.004: the relative norm is the first cyclic Tate differential

Modified by Worker 744, 16 November 2026 UTC: extract only the proof of
M074.004 from
`Nyll/ClassFieldTheory/AbstractClassFieldTheory/Reciprocity/CyclicNormQuotient.lean`
(lines 170–199) at fbd320cd8b1b06487c58227e92eb135794267709. Prefix the
namespace with `Langlands.NYLL`, import the published statement modules of
M074.004 and M073.005 and the published M073.004 proof module, give the
theorem the published Statement applied to the source parameters as its
type and unfold it first. Write `extensionSubgroup K L hLK` as its exact
`Subgroup.subgroupOf` body. The source closes the goal with the M073.005
theorem `extensionFixedRepresentation_norm_coe`, whose proof is not yet in the
Library; this file proves that published M073.005 Statement in the private
local lemma `extensionFixedRepresentation_norm_coe_local`, by the source
M073.005 proof steps (without its rewrite by the `rfl` lemma M024.010), and
uses it in place of the source theorem. All other source steps are retained.
The source `KummerTheory`, `CyclicCohomology` and `CategoryTheory` opens are
kept; all other source declarations are omitted.
See the paired Markdown and `licenses/NYLL/LICENSE` and `licenses/NYLL/NOTICE`.
-/

namespace Langlands.NYLL.ClassFormation

open KummerTheory CyclicCohomology CategoryTheory

noncomputable section

-- Mathlib's `Rep ℤ G` currently fixes the acting group to universe zero.
variable {G : IntegralRepGroupType} [Group G] [TopologicalSpace G]

/-- Private local proof of the published M073.005 Statement: the norm in the
descended representation is the actual relative norm on the underlying fixed
coefficient. It stands in for the source theorem
`extensionFixedRepresentation_norm_coe`, whose proof is not yet in the
Library. -/
private theorem extensionFixedRepresentation_norm_coe_local
    (A : Rep ℤ G) (K L : ClosedSubgroup G)
    (hLK : L.toSubgroup ≤ K.toSubgroup)
    (hnormal : ((L.toSubgroup.subgroupOf K.toSubgroup)).Normal)
    [Finite (K.toSubgroup ⧸ (L.toSubgroup.subgroupOf K.toSubgroup))]
    (a : (extensionFixedRepresentation A K L hLK hnormal).V) :
    extensionFixedRepresentation_norm_coeStatement A K L hLK hnormal a := by
  unfold extensionFixedRepresentation_norm_coeStatement
  let := hnormal
  let := Fintype.ofFinite
    (K.toSubgroup ⧸ (L.toSubgroup.subgroupOf K.toSubgroup))
  simp only [Rep.norm, Representation.norm]
  let M := extensionFixedRepresentation A K L hLK hnormal
  let : Module ℤ M.V := M.hV2
  change ((∑ q, M.ρ q) a).1 =
    ∑ q, relativeCosetAction A K L hLK
      (extensionFixedRepresentationEquiv A K L hLK hnormal a) q
  rw [LinearMap.sum_apply]
  let coeToAmbient :
      (extensionFixedRepresentation A K L hLK hnormal).V →+ A.V :=
    { toFun := fun x => x.1
      map_zero' := rfl
      map_add' := fun _ _ => rfl }
  change coeToAmbient (∑ q, M.ρ q a) =
    ∑ q, relativeCosetAction A K L hLK
      (extensionFixedRepresentationEquiv A K L hLK hnormal a) q
  rw [map_sum]
  apply Finset.sum_congr rfl
  intro q _
  exact extensionFixedRepresentation_action_coe A K L hLK hnormal q a

/-- Under the fixed-cycle equivalence, the actual relative norm is the
first differential in the cyclic Tate complex. -/
theorem cyclicFixedCycleEquiv_relativeNorm
    (A : Rep ℤ G)
    (K L : ClosedSubgroup G) (hLK : L.toSubgroup ≤ K.toSubgroup)
    (hnormal : ((L.toSubgroup.subgroupOf K.toSubgroup)).Normal)
    (hfinite : Finite (K.toSubgroup ⧸ (L.toSubgroup.subgroupOf K.toSubgroup)))
    (g : K.toSubgroup ⧸ (L.toSubgroup.subgroupOf K.toSubgroup))
    (hg : ∀ x, x ∈ Subgroup.zpowers g)
    (a : ambientFixedAddSubgroup A L) :
    cyclicFixedCycleEquiv_relativeNormStatement A K L hLK hnormal hfinite g hg a := by
  unfold cyclicFixedCycleEquiv_relativeNormStatement
  intro instNormal instFinite instFintype instCyclic instCommGroup M T
  apply Subtype.ext
  apply Subtype.ext
  exact (extensionFixedRepresentation_norm_coe_local
    A K L hLK hnormal
      ((extensionFixedRepresentationEquiv A K L hLK hnormal).symm a)).symm

end
end Langlands.NYLL.ClassFormation
