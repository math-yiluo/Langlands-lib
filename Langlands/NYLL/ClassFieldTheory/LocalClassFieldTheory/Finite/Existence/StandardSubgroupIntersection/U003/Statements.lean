/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

/-
Modified by Worker 548, 14 November 2026: extract the complete type of
M403.003, StandardSubgroupIntersection.lean lines 135–154, from commit
fbd320cd8b1b06487c58227e92eb135794267709. Prefix the namespace with
Langlands.NYLL, universally close the source telescope as a Prop-valued
definition with the Statement suffix, and omit the proof. Replace broad
source imports with the focused definitions used by the target. Disable
the unused-variable linter only for this definition to retain the source
hypothesis names. See the paired Markdown for every modification.
The original LICENSE and NOTICE remain in licenses/NYLL/.
-/

import Langlands.NYLL.ClassFieldTheory.AbstractClassFieldTheory.Reciprocity.FiniteAbelianSubextension.Compositum
import Langlands.NYLL.ClassFieldTheory.AbstractClassFieldTheory.Reciprocity.FiniteAbelianSubextension.NormSubgroup.Definitions
import Langlands.NYLL.ClassFieldTheory.LocalClassFieldTheory.Finite.LocalReciprocity.IntrinsicAbsoluteData.Initial.Definitions
import Langlands.NYLL.ClassFieldTheory.LocalClassFieldTheory.Finite.LocalReciprocity.SeparableUnitsNorm.BaseUnits.Definitions
import Langlands.NYLL.ClassFieldTheory.LocalClassFieldTheory.Finite.Existence.UnramifiedNormSubgroup.U011.Definitions
import Langlands.NYLL.ValuedFieldTheory.LocalField.NonarchimedeanLocalField.StandardOpenSubgroups.UniformizerPrincipalSubgroup

/-!
# Finite abelian compositum standard norm containment: proposition target

Source: M403.003, the complete theorem telescope at lines 135–154 of
`Nyll/ClassFieldTheory/LocalClassFieldTheory/Finite/Existence/StandardSubgroupIntersection.lean`.
-/

namespace Langlands.NYLL.LocalClassFieldTheory

open scoped ValuativeRel
open LocalFieldTheory
open LocalFieldTheory.IsNonarchimedeanLocalField

set_option linter.unusedVariables false in
/-- The same standard-subgroup containment while retaining both inputs and
their compositum as finite abelian subextensions. -/
def finiteAbelianCompositum_normSubgroup_le_of_standardStatement : Prop :=
  ∀ (K : Type) [Field K] [ValuativeRel K] [TopologicalSpace K]
    [IsNonarchimedeanLocalField K]
    (H : Subgroup Kˣ)
    (ϖ : Kˣ) (d n : ℕ)
    (hϖ : valuationMap K (Additive.ofMul ϖ) = 1)
    (hstandard : LocalFieldTheory.uniformizerPrincipalSubgroup K ϖ d n ≤ H)
    (U T : ClassFormation.FiniteAbelianSubextension
      (intrinsicAbstractBase K))
    (hUle :
      (U.normSubgroup (intrinsicAbsoluteUnits K)).map
          (baseUnitsEquivGaloisAmbientFixed K (SeparableClosure K)).symm.toAddMonoidHom ≤
        (unramifiedNormSubgroup K d).toAddSubgroup)
    (hTle :
      (T.normSubgroup (intrinsicAbsoluteUnits K)).map
          (baseUnitsEquivGaloisAmbientFixed K (SeparableClosure K)).symm.toAddMonoidHom ≤
        (LocalFieldTheory.uniformizerPrincipalSubgroup K ϖ 1 n).toAddSubgroup),
    (U.compositum T).normSubgroup (intrinsicAbsoluteUnits K) ≤
      H.toAddSubgroup.map
        (baseUnitsEquivGaloisAmbientFixed K (SeparableClosure K)).toAddMonoidHom

end Langlands.NYLL.LocalClassFieldTheory
