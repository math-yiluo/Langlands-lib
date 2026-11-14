/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import Langlands.NYLL.ClassFieldTheory.LocalClassFieldTheory.Finite.Existence.NormSubgroupOrderEmbedding.FixedFieldAbelian.Statements
import Langlands.NYLL.ClassFieldTheory.LocalClassFieldTheory.Finite.Existence.LocalAbsoluteData.U005.Proofs
import Langlands.NYLL.ClassFieldTheory.LocalClassFieldTheory.Finite.Existence.NormSubgroupOrderEmbedding.AbsoluteBase.U001.Proofs
import Langlands.NYLL.ClassFieldTheory.LocalClassFieldTheory.Finite.Existence.NormSubgroupOrderEmbedding.AbsoluteBase.U002.Proofs
import Langlands.NYLL.ClassFieldTheory.LocalClassFieldTheory.Finite.LocalReciprocity.FiniteAbstractFixedField.Initial.U002.Proofs
import Langlands.NYLL.ClassFieldTheory.LocalClassFieldTheory.Finite.LocalReciprocity.FiniteAbstractFixedField.Finiteness.U005.Proofs
import Langlands.NYLL.ClassFieldTheory.LocalClassFieldTheory.Finite.LocalReciprocity.GaloisExtensionQuotient.Quotient.Definitions

/-!
# NYLL M300.004: the represented fixed field is abelian Galois

Adapted by Worker 667 from NYLL commit
`fbd320cd8b1b06487c58227e92eb135794267709`, M300.004, lines 83–124
of `Nyll/ClassFieldTheory/LocalClassFieldTheory/Finite/Existence/NormSubgroupOrderEmbedding.lean`.
The complete source telescope is retained and the theorem proves the published
Prop target. Source prerequisites are imported from their published proof
modules; subgroup membership is unfolded definitionally instead of rewriting
with the source membership lemma. See the paired Markdown for the proof and
modification record. Original license and notices are retained in
`licenses/NYLL/LICENSE` and `licenses/NYLL/NOTICE`.
-/

noncomputable section

namespace Langlands.NYLL.LocalClassFieldTheory

open RamificationTheory CyclicCohomology ClassFormation

/-- The fixed field represented by a finite abelian subextension is
abelian Galois over the original field. -/
theorem finiteAbelianSubextension_fixedField_isAbelianGalois
    (K : Type) [Field K]
    (L : FiniteAbelianSubextension (intrinsicAbstractBase K)) :
    finiteAbelianSubextension_fixedField_isAbelianGaloisStatement K L := by
  let E := abstractFixedField K (SeparableClosure K) L.field
  let : Finite ((baseField (intrinsicAbsoluteGalois K)).toSubgroup ⧸
      extensionSubgroup (baseField (intrinsicAbsoluteGalois K)) L.field
        (le_baseField L.field)) :=
    finiteAbelianSubextension_finite_over_absoluteBase K L
  let : FiniteDimensional K E :=
    abstractFixedField_finiteDimensional
      K (SeparableClosure K) L.field inferInstance
  let : IsGalois K E :=
    abstractFixedField_isGalois_of_base_normal K L.field
      (finiteAbelianSubextension_normal_over_absoluteBase K L)
  let : (extensionSubgroup
      (intrinsicAbstractBase K) L.field L.below).Normal := L.normal
  let e : L.extensionQuotient ≃* Gal(E / K) := by
    let e₀ := baseFixingExtensionQuotientEquivGaloisGroup
      K (SeparableClosure K) E
    have hclosed : closedFixingSubgroup K (SeparableClosure K) E =
        L.field :=
      closedFixingSubgroup_abstractFixedField_eq
        K (SeparableClosure K) L.field
    have hsub :
        extensionSubgroup (intrinsicAbstractBase K)
            (closedFixingSubgroup K (SeparableClosure K) E)
            (fixingSubgroupLeBase K (SeparableClosure K) E) =
          extensionSubgroup (intrinsicAbstractBase K) L.field L.below := by
      ext σ
      change (σ.1 ∈ closedFixingSubgroup K (SeparableClosure K) E) ↔
        (σ.1 ∈ L.field)
      exact SetLike.ext_iff.mp hclosed σ.1
    exact L.extensionQuotientMulEquiv.trans
      ((QuotientGroup.quotientMulEquivOfEq hsub.symm).trans e₀)
  refine { is_comm.comm := fun σ τ ↦ ?_ }
  exact e.symm.injective (by
    simpa only [map_mul] using
      mul_comm (e.symm σ) (e.symm τ))

end Langlands.NYLL.LocalClassFieldTheory
