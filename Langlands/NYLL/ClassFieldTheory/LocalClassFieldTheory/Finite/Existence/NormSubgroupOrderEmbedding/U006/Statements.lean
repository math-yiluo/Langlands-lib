/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import Langlands.NYLL.ClassFieldTheory.AbstractClassFieldTheory.Degree.Norm.RelativeNorm.Definitions
import Langlands.NYLL.ClassFieldTheory.LocalClassFieldTheory.Finite.LocalReciprocity.IntrinsicAbsoluteData.Initial.Definitions
import Langlands.NYLL.ClassFieldTheory.LocalClassFieldTheory.Finite.LocalReciprocity.AbstractFixedFieldUnits.Initial.Definitions
import Langlands.NYLL.GaloisCohomology.Cyclic.NormKernelVanishing.Extension.Definitions

/-!
# Abstract fixed-field relative norm: value target

Modified by Worker 537, 14 November 2026: extract the statement of M300.006
from `Nyll/ClassFieldTheory/LocalClassFieldTheory/Finite/Existence/NormSubgroupOrderEmbedding.lean`
at commit `fbd320cd8b1b06487c58227e92eb135794267709`, prefix the namespace with
`Langlands.NYLL`, add the `Statement` suffix, replace the theorem and proof
with a Prop-valued definition, and use focused support imports.
The complete source telescope, norm expression and coercions are retained.
See the paired Markdown and `licenses/NYLL/LICENSE` and `licenses/NYLL/NOTICE`.
-/

noncomputable section

namespace Langlands.NYLL.LocalClassFieldTheory

open CyclicCohomology ClassFormation

/-- Target identifying the value of the actual relative norm of an abstract
fixed-field unit with its ordinary field norm in the separable closure. -/
def relativeNorm_abstractFixedFieldUnit_val_of_isGaloisStatement
    (K : Type) [Field K]
    (H : ClosedSubgroup (intrinsicAbsoluteGalois K))
    (hH : H.toSubgroup ≤ (intrinsicAbstractBase K).toSubgroup)
    [Finite ((intrinsicAbstractBase K).toSubgroup ⧸
      extensionSubgroup (intrinsicAbstractBase K) H hH)]
    [FiniteDimensional K
      (abstractFixedField K (SeparableClosure K) H)]
    [IsGalois K (abstractFixedField K (SeparableClosure K) H)]
    (x : (abstractFixedField K (SeparableClosure K) H)ˣ) : Prop :=
    ((Additive.toMul
      ((relativeNorm (intrinsicAbsoluteUnits K) (intrinsicAbstractBase K)
        H hH (abstractFixedFieldUnitsEquivGaloisFixed
          K (SeparableClosure K) H (Additive.ofMul x))).1 :
        Additive (SeparableClosure K)ˣ) : (SeparableClosure K)ˣ) :
      SeparableClosure K) =
      algebraMap K (SeparableClosure K)
        (Algebra.norm K
          (x : abstractFixedField K (SeparableClosure K) H))

end Langlands.NYLL.LocalClassFieldTheory
