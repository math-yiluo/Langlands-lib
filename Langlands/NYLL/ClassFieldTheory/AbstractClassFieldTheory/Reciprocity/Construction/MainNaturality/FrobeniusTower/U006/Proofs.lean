/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

/-
Modifications by Worker 5264, 15 November 2026:
Extract the proof of M066.006 from
Nyll/ClassFieldTheory/AbstractClassFieldTheory/Reciprocity/Construction/MainNaturality.lean
at fbd320cd8b1b06487c58227e92eb135794267709. Add the Langlands.NYLL
namespace prefix, import the published FrobeniusTower Statements module and
the published proofs of M009.005 zHatMulNat_injective, M010.027
residueDegreeCardinal_eq_coe, M010.036
relativeResidueDegreeCardinal_mul_residueDegreeCardinal and M011.008
residueDegree_nsmul_normalizedDegree, and give the theorem the published
proposition finiteReciprocityNaturalityFrobeniusTowerMap_degreeStatement as
its type. The final source step applies
frobeniusRestrictionNaturality_normalizedDegree (M011.019), whose proof is
not yet published, nor are the proofs of the two results it uses,
FiniteResidueAbstractExtension.residueDegree_mul_absoluteResidueDegree
(M011.017) and FiniteAbstractExtension.relativeResidueDegreeCardinal_eq_coe
(M010.103). Their source proofs (Degree/Frobenius.lean and Degree/Fields.lean)
are reproduced as the private theorems
relativeResidueDegreeCardinal_eq_coe_aux,
residueDegree_mul_absoluteResidueDegree_aux and
frobeniusRestrictionNaturality_normalizedDegree_aux. Because the published
results used by these proofs are stated as Prop-valued definitions, rewrites
with them go through local equations with the unfolded types. The rest of the
proofs are the source's. Omit open KummerTheory, open CategoryTheory,
open scoped BigOperators, the noncomputable section and all other source
declarations.
The original LICENSE and NOTICE are retained in licenses/NYLL/.
-/

import Langlands.NYLL.ClassFieldTheory.AbstractClassFieldTheory.Reciprocity.Construction.MainNaturality.FrobeniusTower.Statements
import Langlands.NYLL.ClassFieldTheory.AbstractClassFieldTheory.Degree.Fields.AbstractExtension.U036.Proofs
import Langlands.NYLL.ClassFieldTheory.AbstractClassFieldTheory.Degree.Fields.FiniteResidue.U027.Proofs
import Langlands.NYLL.ClassFieldTheory.AbstractClassFieldTheory.Degree.Frobenius.NormalizedDegree.U008.Proofs
import Langlands.NYLL.GaloisCohomology.ProfiniteIntegers.ProfiniteInteger.U005.Proofs

/-!
# The Frobenius tower map multiplies normalized degree by `f`
-/

universe u

namespace Langlands.NYLL.ClassFormation

open CyclicCohomology

variable {G : Type u} [Group G] [TopologicalSpace G]

namespace DegreeData

/-- The source proof of M010.103
`FiniteAbstractExtension.relativeResidueDegreeCardinal_eq_coe` (not yet
published): for a finite extension, the cardinal-valued relative residue
degree is the cardinal cast of the positive natural residue degree. -/
private theorem relativeResidueDegreeCardinal_eq_coe_aux
    (E : FiniteAbstractExtension G) (D : DegreeData G) :
    E.toAbstractExtension.relativeResidueDegreeCardinal D =
      ((E.residueDegree D : ℕ) : Cardinal) := by
  change Cardinal.mk
    (↥(E.base.toSubgroup.map D.degree.toMonoidHom) ⧸
      (E.field.toSubgroup.map D.degree.toMonoidHom).subgroupOf
        (E.base.toSubgroup.map D.degree.toMonoidHom)) =
      (Nat.card
        (↥(E.base.toSubgroup.map D.degree.toMonoidHom) ⧸
          (E.field.toSubgroup.map D.degree.toMonoidHom).subgroupOf
            (E.base.toSubgroup.map D.degree.toMonoidHom)) : Cardinal)
  exact (Nat.cast_card).symm

/-- The source proof of M011.017
`FiniteResidueAbstractExtension.residueDegree_mul_absoluteResidueDegree`
(not yet published): for a finite extension, its positive residue degree
times the absolute residue degree of the base is the absolute residue degree
of the field. -/
private theorem residueDegree_mul_absoluteResidueDegree_aux
    (D : DegreeData G) (E : FiniteResidueAbstractExtension D) :
    (E.residueDegree : ℕ) * (E.base.residueDegree : ℕ) =
      (E.field.residueDegree : ℕ) := by
  have h :=
    AbstractExtension.relativeResidueDegreeCardinal_mul_residueDegreeCardinal
      E.toFiniteAbstractExtension.toAbstractExtension D
  change E.toFiniteAbstractExtension.toAbstractExtension.relativeResidueDegreeCardinal D *
      D.residueDegreeCardinal E.base.field =
    D.residueDegreeCardinal E.field.field at h
  rw [relativeResidueDegreeCardinal_eq_coe_aux E.toFiniteAbstractExtension D] at h
  change ((E.residueDegree : ℕ) : Cardinal) *
      D.residueDegreeCardinal E.base.field =
    D.residueDegreeCardinal E.field.field at h
  have hbase : D.residueDegreeCardinal E.base.field =
      ((E.base.residueDegree : ℕ) : Cardinal) :=
    E.base.residueDegreeCardinal_eq_coe
  have hfield : D.residueDegreeCardinal E.field.field =
      ((E.field.residueDegree : ℕ) : Cardinal) :=
    E.field.residueDegreeCardinal_eq_coe
  rw [hbase, hfield] at h
  exact_mod_cast h

/-- The source proof of M011.019
`frobeniusRestrictionNaturality_normalizedDegree` (not yet published): on
`G_L`, the normalized degree maps satisfy `d_K = f_{L|K} d_L`. -/
private theorem frobeniusRestrictionNaturality_normalizedDegree_aux
    (D : DegreeData G) (E : FiniteResidueAbstractExtension D)
    (l : E.field.field.toSubgroup) :
    (D.normalizedDegree E.base (Subgroup.inclusion E.below l)).toAdd =
      (E.residueDegree : ℕ) •
        (D.normalizedDegree E.field l).toAdd := by
  apply zHatMulNat_injective E.base.residueDegree.property
  change (E.base.residueDegree : ℕ) •
      (D.normalizedDegree E.base (Subgroup.inclusion E.below l)).toAdd =
    (E.base.residueDegree : ℕ) •
      ((E.residueDegree : ℕ) •
        (D.normalizedDegree E.field l).toAdd)
  have hbase : (E.base.residueDegree : ℕ) •
      (D.normalizedDegree E.base (Subgroup.inclusion E.below l)).toAdd =
      (D.degree (Subgroup.inclusion E.below l).1).toAdd :=
    D.residueDegree_nsmul_normalizedDegree E.base (Subgroup.inclusion E.below l)
  have hfield : (E.field.residueDegree : ℕ) •
      (D.normalizedDegree E.field l).toAdd = (D.degree l.1).toAdd :=
    D.residueDegree_nsmul_normalizedDegree E.field l
  rw [hbase]
  change (D.degree l.1).toAdd = _
  rw [smul_smul, Nat.mul_comm (E.base.residueDegree : ℕ),
    residueDegree_mul_absoluteResidueDegree_aux D E, hfield]

/-- Frobenius residue-degree compatibility's normalized-degree square on the two infinite
Frobenius quotients. -/
theorem finiteReciprocityNaturalityFrobeniusTowerMap_degree
    (D : DegreeData G) [IsTopologicalGroup G]
    (E : DegreeData.FiniteResidueAbstractExtension D)
    (L L' : ClosedSubgroup G)
    (hLK : L.toSubgroup ≤ E.base.toSubgroup)
    (hL'K' : L'.toSubgroup ≤ E.field.toSubgroup)
    (hL'L : L'.toSubgroup ≤ L.toSubgroup)
    [hLnormal : (extensionSubgroup E.base.field L hLK).Normal]
    [hL'normal : (extensionSubgroup E.field.field L' hL'K').Normal]
    (q : E.field.toSubgroup ⧸
      D.extensionInertiaWithin E.field.field L' hL'K') :
    finiteReciprocityNaturalityFrobeniusTowerMap_degreeStatement
      D E L L' hLK hL'K' hL'L q := by
  refine Quotient.inductionOn' q ?_
  intro k'
  change (D.normalizedDegree E.base (Subgroup.inclusion E.below k')).toAdd =
    (E.residueDegree : ℕ) • (D.normalizedDegree E.field k').toAdd
  -- The source applies M011.019 `frobeniusRestrictionNaturality_normalizedDegree`.
  exact frobeniusRestrictionNaturality_normalizedDegree_aux D E k'

end DegreeData

end Langlands.NYLL.ClassFormation
