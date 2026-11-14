/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

/-
Modifications by Worker 56, 13 November 2026:
Extract only the proof of M288.001
AmbientEmbeddedFixedFieldPresentation.quotientRestriction from
Nyll/ClassFieldTheory/LocalClassFieldTheory/Finite/LocalReciprocity/
FixedFieldIntrinsicReciprocity/NormRestriction.lean at
fbd320cd8b1b06487c58227e92eb135794267709, under the source name with the
Langlands.NYLL prefix, proving the published statement. Introduce the
statement's binders; replace the rewrite with the M086.020 theorem
normResidueNaturalityAbelianizedRestriction_of_mk by the local identity hof,
proved by Abelianization.map_of from the published M086.019 definition (an
Abelianization.map); and prove the two representative identities hmk by
rfl, since the published extensionQuotientMulEquiv is MulEquiv.refl and
extensionQuotientMk is QuotientGroup.mk'. The rest of the source tactic
proof is unchanged.
The original LICENSE and NOTICE are retained in licenses/NYLL/.

Modifications by Worker 699, 14 November 2026:
Adopt Worker 56's shared proof draft without changes to its proof body.
Check the original correspondence and the published defining equations;
retain the focused statement import and all upstream attribution.
-/

import Langlands.NYLL.ClassFieldTheory.LocalClassFieldTheory.Finite.LocalReciprocity.FixedFieldIntrinsicReciprocity.NormRestriction.U001.Statements

namespace Langlands.NYLL.LocalClassFieldTheory

open Langlands.NYLL.CyclicCohomology Langlands.NYLL.ClassFormation
open scoped IsMulCommutative

/-- A compatible restriction of concrete embedded Galois actions induces the
corresponding restriction map on ambient finite quotient representatives. -/
theorem AmbientEmbeddedFixedFieldPresentation.quotientRestriction :
    AmbientEmbeddedFixedFieldPresentation.quotientRestrictionStatement := by
  intro K K' L L' _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _
    jLower jUpper lower upper hH'H hJ'J _ _ _ _ _ _ _
    restrictActual hbase hcompat z
  let qLower :=
    lower.extension.extensionQuotientMulEquiv.symm.trans
      lower.quotientEquiv
  let qUpper :=
    upper.extension.extensionQuotientMulEquiv.symm.trans
      upper.quotientEquiv
  obtain ⟨q, rfl⟩ := QuotientGroup.mk_surjective z
  obtain ⟨sigma, rfl⟩ := QuotientGroup.mk_surjective q
  change
    restrictActual
        ((Abelianization.equivOfComm (H := Gal(L' / K'))).symm
          (qUpper.abelianizationCongr
            (Abelianization.of (QuotientGroup.mk sigma)))) =
      (Abelianization.equivOfComm (H := Gal(L / K))).symm
        (qLower.abelianizationCongr
          (normResidueNaturalityAbelianizedRestriction
            lower.base.field upper.base.field
            lower.extension.field upper.extension.field
            lower.extension.below upper.extension.below
            hH'H hJ'J (Abelianization.of (QuotientGroup.mk sigma))))
  have hof :
      normResidueNaturalityAbelianizedRestriction
          lower.base.field upper.base.field
          lower.extension.field upper.extension.field
          lower.extension.below upper.extension.below
          hH'H hJ'J (Abelianization.of (QuotientGroup.mk sigma)) =
        Abelianization.of
          (QuotientGroup.mk (Subgroup.inclusion hH'H sigma)) :=
    Abelianization.map_of _ _
  rw [hof, abelianizationCongr_of, abelianizationCongr_of]
  change
    restrictActual (qUpper (QuotientGroup.mk sigma)) =
      qLower (QuotientGroup.mk (Subgroup.inclusion hH'H sigma))
  have hqUpper_mk :
      qUpper (QuotientGroup.mk sigma) =
        upper.quotientEquiv
          (upper.extension.extensionQuotientMk sigma) := by
    dsimp [qUpper]
    have hmk :
        upper.extension.extensionQuotientMulEquiv.symm
            (QuotientGroup.mk sigma) =
          upper.extension.extensionQuotientMk sigma :=
      rfl
    rw [hmk]
  have hqLower_mk :
      qLower (QuotientGroup.mk (Subgroup.inclusion hH'H sigma)) =
        lower.quotientEquiv
          (lower.extension.extensionQuotientMk
            (Subgroup.inclusion hH'H sigma)) := by
    dsimp [qLower]
    have hmk :
        lower.extension.extensionQuotientMulEquiv.symm
            (QuotientGroup.mk (Subgroup.inclusion hH'H sigma)) =
          lower.extension.extensionQuotientMk
            (Subgroup.inclusion hH'H sigma) :=
      rfl
    rw [hmk]
  apply AlgEquiv.ext
  intro x
  apply jLower.injective
  calc
    jLower
        (restrictActual
          (qUpper (QuotientGroup.mk sigma)) x) =
        jUpper
          ((qUpper (QuotientGroup.mk sigma))
            (algebraMap L L' x)) :=
      hcompat (qUpper (QuotientGroup.mk sigma)) x
    _ = jUpper
          (upper.quotientEquiv
            (upper.extension.extensionQuotientMk sigma)
            (algebraMap L L' x)) := by
      rw [hqUpper_mk]
    _ = sigma.1.1
        (jUpper (algebraMap L L' x)) :=
      upper.quotientEquiv_mk_apply sigma (algebraMap L L' x)
    _ = (Subgroup.inclusion hH'H sigma).1.1
        (jLower x) := by
      rw [hbase x]
      change sigma.1.1 (jLower x) = sigma.1.1 (jLower x)
      rfl
    _ = jLower
        (lower.quotientEquiv
          (lower.extension.extensionQuotientMk
            (Subgroup.inclusion hH'H sigma)) x) :=
      (lower.quotientEquiv_mk_apply
        (Subgroup.inclusion hH'H sigma) x).symm
    _ = jLower
        (qLower (QuotientGroup.mk
          (Subgroup.inclusion hH'H sigma)) x) := by
      rw [hqLower_mk]

end Langlands.NYLL.LocalClassFieldTheory
