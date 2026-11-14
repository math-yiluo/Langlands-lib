/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import Langlands.NYLL.ClassFieldTheory.AbstractClassFieldTheory.Degree.Norm.RelativeNorm.Definitions
import Langlands.NYLL.ClassFieldTheory.LocalClassFieldTheory.Finite.LocalReciprocity.IntrinsicAbsoluteData.Initial.Definitions
import Langlands.NYLL.ClassFieldTheory.LocalClassFieldTheory.Finite.LocalReciprocity.AbstractFixedFieldUnits.Initial.Definitions
import Langlands.NYLL.ClassFieldTheory.LocalClassFieldTheory.Finite.LocalReciprocity.SeparableUnitsNorm.BaseUnits.Definitions
import Langlands.NYLL.GaloisCohomology.Cyclic.NormKernelVanishing.Extension.Definitions
import Langlands.NYLL.ValuedFieldTheory.LocalField.NormUnits.U002.Definitions

/-!
# Abstract fixed-field relative norm: base-unit target

Modified by Worker 537, 14 November 2026: extract the statement of M300.007
from `Nyll/ClassFieldTheory/LocalClassFieldTheory/Finite/Existence/NormSubgroupOrderEmbedding.lean`
at commit `fbd320cd8b1b06487c58227e92eb135794267709`, prefix the namespace with
`Langlands.NYLL`, add the `Statement` suffix, replace the theorem and proof
with a Prop-valued definition, and use focused support imports.
The complete source telescope, norm expression and coercions are retained.
See the paired Markdown and `licenses/NYLL/LICENSE` and `licenses/NYLL/NOTICE`.
-/

noncomputable section

namespace Langlands.NYLL.LocalClassFieldTheory

open LocalFieldTheory CyclicCohomology ClassFormation

/-- Target identifying the actual relative norm of an abstract fixed-field
unit, transported back to base units, with the ordinary norm on units. -/
def baseUnitsEquivGaloisAmbientFixed_symm_relativeNorm_abstractFixedFieldUnit_eq_normUnitsStatement
    (K : Type) [Field K]
    (H : ClosedSubgroup (intrinsicAbsoluteGalois K))
    (hH : H.toSubgroup ≤ (intrinsicAbstractBase K).toSubgroup)
    [Finite ((intrinsicAbstractBase K).toSubgroup ⧸
      extensionSubgroup (intrinsicAbstractBase K) H hH)]
    [FiniteDimensional K
      (abstractFixedField K (SeparableClosure K) H)]
    [IsGalois K (abstractFixedField K (SeparableClosure K) H)]
    (x : (abstractFixedField K (SeparableClosure K) H)ˣ) : Prop :=
    (baseUnitsEquivGaloisAmbientFixed K (SeparableClosure K)).symm
      (relativeNorm (intrinsicAbsoluteUnits K) (intrinsicAbstractBase K)
        H hH (abstractFixedFieldUnitsEquivGaloisFixed
          K (SeparableClosure K) H (Additive.ofMul x))) =
      Additive.ofMul
        (normUnits K (abstractFixedField K (SeparableClosure K) H) x)

end Langlands.NYLL.LocalClassFieldTheory
