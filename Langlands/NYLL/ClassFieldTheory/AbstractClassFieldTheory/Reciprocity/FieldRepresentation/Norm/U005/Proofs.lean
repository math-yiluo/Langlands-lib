/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import Langlands.NYLL.ClassFieldTheory.AbstractClassFieldTheory.Reciprocity.FieldRepresentation.Norm.Statements
import Langlands.NYLL.ClassFieldTheory.AbstractClassFieldTheory.Reciprocity.FieldRepresentation.Action.U004.Proofs

/-!
# NYLL M073.005: the norm of the fixed representation is the relative norm

Modified by Worker 744, 16 November 2026 UTC: extract only the proof of
M073.005 from
`Nyll/ClassFieldTheory/AbstractClassFieldTheory/Reciprocity/FieldRepresentation.lean`
(lines 102–139) at fbd320cd8b1b06487c58227e92eb135794267709. Prefix the
namespace with `Langlands.NYLL`, import the published Norm Statements module
and the published M073.004 proof module, give the theorem the published
Statement applied to the source parameters as its type and unfold it first.
Write `extensionSubgroup K L hLK` as its exact `Subgroup.subgroupOf` body.
Drop the source step `rw [relativeNorm_apply_coe]`: that equation (M024.010)
holds by `rfl`, and the following `change` reaches the same goal by
definitional unfolding, so the proof does not depend on the M024.010 proof.
Drop `relativeNormValue` from the source `simp only` list for the same
reason. All other source steps are retained. The source opens of
`KummerTheory`, `CyclicCohomology` and scoped `BigOperators` are kept; all
other source declarations are omitted.
See the paired Markdown and `licenses/NYLL/LICENSE` and `licenses/NYLL/NOTICE`.
-/

namespace Langlands.NYLL.ClassFormation

open KummerTheory CyclicCohomology

noncomputable section

open scoped BigOperators

-- Mathlib's `Rep ℤ G` currently fixes the acting group to universe zero.
variable {G : IntegralRepGroupType} [Group G] [TopologicalSpace G]

/-- The norm in the descended representation is the actual relative norm
on the underlying fixed coefficient. -/
theorem extensionFixedRepresentation_norm_coe
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

end
end Langlands.NYLL.ClassFormation
