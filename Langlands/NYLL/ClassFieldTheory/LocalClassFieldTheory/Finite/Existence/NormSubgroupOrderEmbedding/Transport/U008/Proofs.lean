/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import Langlands.NYLL.ClassFieldTheory.LocalClassFieldTheory.Finite.Existence.NormSubgroupOrderEmbedding.Transport.Statements
import Langlands.NYLL.ClassFieldTheory.LocalClassFieldTheory.Finite.Existence.NormSubgroupOrderEmbedding.AbsoluteBase.U001.Proofs
import Langlands.NYLL.ClassFieldTheory.LocalClassFieldTheory.Finite.Existence.NormSubgroupOrderEmbedding.AbsoluteBase.U002.Proofs
import Langlands.NYLL.ClassFieldTheory.LocalClassFieldTheory.Finite.LocalReciprocity.FiniteAbstractFixedField.Finiteness.U005.Proofs
import Langlands.NYLL.ClassFieldTheory.LocalClassFieldTheory.Finite.Existence.LocalAbsoluteData.U005.Proofs
import Langlands.NYLL.ClassFieldTheory.LocalClassFieldTheory.Finite.Existence.NormSubgroupOrderEmbedding.U007.Proofs

/-!
# NYLL M300.008: transport of the actual finite abelian norm subgroup

Adapted by Worker 538 from NYLL commit
`fbd320cd8b1b06487c58227e92eb135794267709`, M300.008, source lines 236–301.
The theorem proves the published proposition target with its complete source
telescope. It reuses M300.007 for the norm identity and compares the two
actual norm images by subgroup extensionality. See the paired Markdown.
Original license and notices: `licenses/NYLL/LICENSE` and `licenses/NYLL/NOTICE`.
-/

noncomputable section

namespace Langlands.NYLL.LocalClassFieldTheory

open LocalFieldTheory CyclicCohomology ClassFormation

/-- Transporting the abstract finite norm subgroup back to `Kˣ` gives
literally the ordinary norm subgroup of the represented fixed field. -/
theorem map_finiteAbelianNormSubgroup_eq_additiveNormSubgroup
    (K : Type) [Field K]
    (L : FiniteAbelianSubextension (intrinsicAbstractBase K)) :
    map_finiteAbelianNormSubgroup_eq_additiveNormSubgroupStatement K L := by
  change (L.normSubgroup (intrinsicAbsoluteUnits K)).map
      (baseUnitsEquivGaloisAmbientFixed K (SeparableClosure K)).symm.toAddMonoidHom =
    additiveNormSubgroup K (abstractFixedField K (SeparableClosure K) L.field)
  let : Finite ((intrinsicAbstractBase K).toSubgroup ⧸
      extensionSubgroup (intrinsicAbstractBase K) L.field L.below) :=
    L.finite
  let : Finite ((baseField (intrinsicAbsoluteGalois K)).toSubgroup ⧸
      extensionSubgroup (baseField (intrinsicAbsoluteGalois K)) L.field
        (le_baseField L.field)) :=
    finiteAbelianSubextension_finite_over_absoluteBase K L
  let E := abstractFixedField K (SeparableClosure K) L.field
  let : FiniteDimensional K E :=
    abstractFixedField_finiteDimensional
      K (SeparableClosure K) L.field inferInstance
  let : IsGalois K E :=
    abstractFixedField_isGalois_of_base_normal K L.field
      (finiteAbelianSubextension_normal_over_absoluteBase K L)
  ext y
  constructor
  · rintro ⟨a, ha, rfl⟩
    rcases ha with ⟨b, rfl⟩
    let u : Eˣ := Additive.toMul
      ((abstractFixedFieldUnitsEquivGaloisFixed
        K (SeparableClosure K) L.field).symm b)
    have hb :
        abstractFixedFieldUnitsEquivGaloisFixed
            K (SeparableClosure K) L.field (Additive.ofMul u) = b := by
      change abstractFixedFieldUnitsEquivGaloisFixed
          K (SeparableClosure K) L.field
            ((abstractFixedFieldUnitsEquivGaloisFixed
              K (SeparableClosure K) L.field).symm b) = b
      exact (abstractFixedFieldUnitsEquivGaloisFixed
        K (SeparableClosure K) L.field).apply_symm_apply b
    rw [← hb]
    change (baseUnitsEquivGaloisAmbientFixed K (SeparableClosure K)).symm
      (relativeNorm (intrinsicAbsoluteUnits K) (intrinsicAbstractBase K)
        L.field L.below (abstractFixedFieldUnitsEquivGaloisFixed
          K (SeparableClosure K) L.field (Additive.ofMul u))) ∈
        additiveNormSubgroup K E
    rw [baseUnitsEquivGaloisAmbientFixed_symm_relativeNorm_abstractFixedFieldUnit_eq_normUnits]
    exact ⟨u, rfl⟩
  · intro hy
    change Additive.toMul y ∈ localNormSubgroup K E at hy
    rcases hy with ⟨u, hu⟩
    refine ⟨baseUnitsEquivGaloisAmbientFixed K (SeparableClosure K)
      (Additive.ofMul (normUnits K E u)), ?_, ?_⟩
    · refine ⟨abstractFixedFieldUnitsEquivGaloisFixed
          K (SeparableClosure K) L.field (Additive.ofMul u), ?_⟩
      apply (baseUnitsEquivGaloisAmbientFixed K (SeparableClosure K)).symm.injective
      change (baseUnitsEquivGaloisAmbientFixed K (SeparableClosure K)).symm
          (relativeNorm (intrinsicAbsoluteUnits K) (intrinsicAbstractBase K)
            L.field L.below (abstractFixedFieldUnitsEquivGaloisFixed
              K (SeparableClosure K) L.field (Additive.ofMul u))) =
        (baseUnitsEquivGaloisAmbientFixed K (SeparableClosure K)).symm
          (baseUnitsEquivGaloisAmbientFixed K (SeparableClosure K)
          (Additive.ofMul (normUnits K E u)))
      rw [baseUnitsEquivGaloisAmbientFixed_symm_relativeNorm_abstractFixedFieldUnit_eq_normUnits,
        (baseUnitsEquivGaloisAmbientFixed K (SeparableClosure K)).symm_apply_apply]
    · change (baseUnitsEquivGaloisAmbientFixed K (SeparableClosure K)).symm
        (baseUnitsEquivGaloisAmbientFixed K (SeparableClosure K)
          (Additive.ofMul (normUnits K E u))) = y
      rw [(baseUnitsEquivGaloisAmbientFixed K (SeparableClosure K)).symm_apply_apply]
      exact congrArg Additive.ofMul hu

end Langlands.NYLL.LocalClassFieldTheory
