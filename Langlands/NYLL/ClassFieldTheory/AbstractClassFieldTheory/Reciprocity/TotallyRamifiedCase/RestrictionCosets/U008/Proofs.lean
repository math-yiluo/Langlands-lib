/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import Langlands.NYLL.ClassFieldTheory.AbstractClassFieldTheory.Reciprocity.TotallyRamifiedCase.RestrictionCosets.Statements

/-!
# NYLL M080.008: equal restrictions commute below the inertia field

Modified by Worker 756, 16 November 2026: extract the proof of M080.008
`FiniteGaloisSubextension.commute_of_same_restriction_of_inertia_le`
(lines 323–407) of
`Nyll/ClassFieldTheory/AbstractClassFieldTheory/Reciprocity/TotallyRamifiedCase/RestrictionCosets.lean`
at `fbd320cd8b1b06487c58227e92eb135794267709`, prefix the namespace with
`Langlands.NYLL`, replace the source import by the published statement
module, and state the theorem as the published Statement applied to the
source parameters. The two uses of `mem_extensionSubgroup_iff` are replaced
by Mathlib's `Subgroup.mem_subgroupOf`, which states the same equivalence
for the abbreviation `extensionSubgroup`. The paired Markdown records every
modification. See `licenses/NYLL/LICENSE` and `licenses/NYLL/NOTICE`.
-/

noncomputable section

namespace Langlands.NYLL.ClassFormation

open KummerTheory
open CyclicCohomology

-- Mathlib's `Rep ℤ G` currently fixes the acting group to universe zero.
variable {G : IntegralRepGroupType} [Group G] [TopologicalSpace G]

namespace FiniteGaloisSubextension

/-- Two auxiliary quotient elements commute when they have the same
restriction and the auxiliary field contains the inertia subgroup. -/
theorem commute_of_same_restriction_of_inertia_le
    (D : DegreeData G) [IsTopologicalGroup G]
    (E : DegreeData.AbstractExtension G)
    (M : FiniteGaloisSubextension E.base)
    (hME : M.field.toSubgroup ≤ E.field.toSubgroup)
    (hIE : (D.fieldInertia E.field).toSubgroup ≤ M.field.toSubgroup)
    [hEnormal :
      (extensionSubgroup E.base E.field E.below).Normal]
    (g t : E.base.toSubgroup ⧸
      extensionSubgroup E.base M.field M.below)
    (hres : abstractReciprocityRestriction
        E.base E.field M.field hME E.below g =
      abstractReciprocityRestriction
        E.base E.field M.field hME E.below t) :
    commute_of_same_restriction_of_inertia_leStatement
      D E M hME hIE g t hres := by
  change Commute g t
  rw [Commute]
  let a : E.base.toSubgroup := Quotient.out g
  let b : E.base.toSubgroup := Quotient.out t
  have ha : (QuotientGroup.mk'
      (extensionSubgroup E.base M.field M.below)) a = g :=
    Quotient.out_eq' g
  have hb : (QuotientGroup.mk'
      (extensionSubgroup E.base M.field M.below)) b = t :=
    Quotient.out_eq' t
  have hcosetE :
      (QuotientGroup.mk'
        (extensionSubgroup E.base E.field E.below)) (a * b) =
      (QuotientGroup.mk'
        (extensionSubgroup E.base E.field E.below)) (b * a) := by
    rw [map_mul, map_mul]
    have haE : (QuotientGroup.mk'
        (extensionSubgroup E.base E.field E.below)) a =
        abstractReciprocityRestriction
          E.base E.field M.field hME E.below g := by
      calc
        (QuotientGroup.mk'
            (extensionSubgroup E.base E.field E.below)) a =
            abstractReciprocityRestriction E.base E.field M.field hME E.below
              ((QuotientGroup.mk'
                (extensionSubgroup E.base M.field M.below)) a) := rfl
        _ = abstractReciprocityRestriction
            E.base E.field M.field hME E.below g :=
          congrArg (abstractReciprocityRestriction
            E.base E.field M.field hME E.below) ha
    have hbE : (QuotientGroup.mk'
        (extensionSubgroup E.base E.field E.below)) b =
        abstractReciprocityRestriction
          E.base E.field M.field hME E.below t := by
      calc
        (QuotientGroup.mk'
            (extensionSubgroup E.base E.field E.below)) b =
            abstractReciprocityRestriction E.base E.field M.field hME E.below
              ((QuotientGroup.mk'
                (extensionSubgroup E.base M.field M.below)) b) := rfl
        _ = abstractReciprocityRestriction
            E.base E.field M.field hME E.below t :=
          congrArg (abstractReciprocityRestriction
            E.base E.field M.field hME E.below) hb
    rw [haE, hbE, hres]
  let z : E.base.toSubgroup := (a * b)⁻¹ * (b * a)
  have hzE : z ∈ extensionSubgroup E.base E.field E.below :=
    QuotientGroup.eq.mp hcosetE
  have hzE' : z.1 ∈ E.field.toSubgroup :=
    Subgroup.mem_subgroupOf.1 hzE
  have hzDegree : D.degree z.1 = 1 := by
    dsimp [z]
    rw [map_mul, map_inv, map_mul, map_mul]
    apply Multiplicative.ext
    change -((D.degree a.1).toAdd + (D.degree b.1).toAdd) +
      ((D.degree b.1).toAdd + (D.degree a.1).toAdd) = 0
    abel
  have hzM : z.1 ∈ M.field.toSubgroup :=
    hIE ⟨hzE', hzDegree⟩
  have hzH : z ∈ extensionSubgroup E.base M.field M.below :=
    Subgroup.mem_subgroupOf.2 hzM
  calc
    g * t = (QuotientGroup.mk'
        (extensionSubgroup E.base M.field M.below)) (a * b) := by
      rw [map_mul, ha, hb]
    _ = (QuotientGroup.mk'
        (extensionSubgroup E.base M.field M.below)) (b * a) :=
      QuotientGroup.eq.mpr hzH
    _ = t * g := by rw [map_mul, ha, hb]

end FiniteGaloisSubextension

end Langlands.NYLL.ClassFormation
