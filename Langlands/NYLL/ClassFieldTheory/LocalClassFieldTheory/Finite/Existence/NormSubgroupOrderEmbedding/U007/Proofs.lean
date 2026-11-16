/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import Langlands.NYLL.ClassFieldTheory.LocalClassFieldTheory.Finite.Existence.NormSubgroupOrderEmbedding.U007.Statements
import Langlands.NYLL.ClassFieldTheory.LocalClassFieldTheory.Finite.Existence.NormSubgroupOrderEmbedding.U006.Proofs
import Langlands.NYLL.ClassFieldTheory.LocalClassFieldTheory.Finite.LocalReciprocity.SeparableUnitsNorm.BaseUnits.U002.Proofs

/-!
# Abstract fixed-field relative norm in base units

Modified by Worker 324, 16 November 2026: extract M300.007 from
`Nyll/ClassFieldTheory/LocalClassFieldTheory/Finite/Existence/NormSubgroupOrderEmbedding.lean`
at commit `fbd320cd8b1b06487c58227e92eb135794267709`, prefix the namespace
with `Langlands.NYLL`, and use focused Library imports. State the theorem as
the published proposition applied to the complete source telescope, unfold
that proposition, and replace the `normUnits_apply_coe` rewrite by `rfl`.
Retain the source extensionality and norm-comparison argument. See the paired
Markdown and the retained attribution in `licenses/NYLL/`.
-/

noncomputable section

namespace Langlands.NYLL.LocalClassFieldTheory

open LocalFieldTheory CyclicCohomology ClassFormation

/-- Transporting the relative norm of an abstract fixed-field unit back to
base units gives the ordinary norm on units, written additively. -/
theorem baseUnitsEquivGaloisAmbientFixed_symm_relativeNorm_abstractFixedFieldUnit_eq_normUnits
    (K : Type) [Field K]
    (H : ClosedSubgroup (intrinsicAbsoluteGalois K))
    (hH : H.toSubgroup ≤ (intrinsicAbstractBase K).toSubgroup)
    [Finite ((intrinsicAbstractBase K).toSubgroup ⧸
      extensionSubgroup (intrinsicAbstractBase K) H hH)]
    [FiniteDimensional K
      (abstractFixedField K (SeparableClosure K) H)]
    [IsGalois K (abstractFixedField K (SeparableClosure K) H)]
    (x : (abstractFixedField K (SeparableClosure K) H)ˣ) :
    baseUnitsEquivGaloisAmbientFixed_symm_relativeNorm_abstractFixedFieldUnit_eq_normUnitsStatement
      K H hH x := by
  unfold baseUnitsEquivGaloisAmbientFixed_symm_relativeNorm_abstractFixedFieldUnit_eq_normUnitsStatement
  apply (baseUnitsEquivGaloisAmbientFixed K (SeparableClosure K)).injective
  rw [(baseUnitsEquivGaloisAmbientFixed K (SeparableClosure K)).apply_symm_apply]
  apply Subtype.ext
  apply Additive.ext
  apply Units.ext
  calc
    _ = algebraMap K (SeparableClosure K)
        (Algebra.norm K
          (x : abstractFixedField K (SeparableClosure K) H)) :=
      relativeNorm_abstractFixedFieldUnit_val_of_isGalois K H hH x
    _ = algebraMap K (SeparableClosure K)
        ((normUnits K (abstractFixedField K (SeparableClosure K) H) x :
          Kˣ) : K) := by
      rfl
    _ = _ :=
      (baseUnitsEquivGaloisAmbientFixed_val K (SeparableClosure K)
        (normUnits K (abstractFixedField K (SeparableClosure K) H) x)).symm

end Langlands.NYLL.LocalClassFieldTheory
