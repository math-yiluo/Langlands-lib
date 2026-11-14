/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import Langlands.NYLL.ClassFieldTheory.AbstractClassFieldTheory.Reciprocity.FiniteAbelianSubextension.NormSubgroup.Definitions
import Langlands.NYLL.ClassFieldTheory.LocalClassFieldTheory.Finite.Existence.NormSubgroupOrderEmbedding.Definitions
import Langlands.NYLL.ClassFieldTheory.LocalClassFieldTheory.Finite.LocalReciprocity.SeparableUnitsNorm.BaseUnits.Definitions
import Langlands.NYLL.GaloisCohomology.Cyclic.TateH0.NormImage.Definitions

/-!
# Native norm subgroup transport and containment targets

Adapted by Worker 538 from NYLL commit
`fbd320cd8b1b06487c58227e92eb135794267709`,
`Nyll/ClassFieldTheory/LocalClassFieldTheory/Finite/Existence/NormSubgroupOrderEmbedding.lean`,
M300.008–.009. The source theorems are extracted as proposition definitions,
without proofs, under `Langlands.NYLL`. See the paired Markdown for the exact
source correspondence, dependency reuse and complete modification record.
The original license and notices are retained in `licenses/NYLL/LICENSE` and
`licenses/NYLL/NOTICE`.
-/

noncomputable section

namespace Langlands.NYLL.LocalClassFieldTheory

open CyclicCohomology

variable (K : Type) [Field K]

/-- Target for identifying the transported abstract finite-abelian norm
subgroup with the additive native norm subgroup of the represented fixed field. -/
def map_finiteAbelianNormSubgroup_eq_additiveNormSubgroupStatement
    (L : ClassFormation.FiniteAbelianSubextension (intrinsicAbstractBase K)) : Prop :=
  (L.normSubgroup (intrinsicAbsoluteUnits K)).map
      (baseUnitsEquivGaloisAmbientFixed K (SeparableClosure K)).symm.toAddMonoidHom =
    additiveNormSubgroup K
      (abstractFixedField K (SeparableClosure K) L.field)

/-- Target for transporting an abstract norm containment to the native norm
subgroup, retaining the source containment as an explicit proof argument. -/
def finiteAbelianNormSubgroup_le_of_abstractNormSubgroup_le_mapStatement
    (L : ClassFormation.FiniteAbelianSubextension (intrinsicAbstractBase K))
    (H : Subgroup Kˣ)
    (h :
      L.normSubgroup (intrinsicAbsoluteUnits K) ≤
        H.toAddSubgroup.map
          (baseUnitsEquivGaloisAmbientFixed K (SeparableClosure K)).toAddMonoidHom) :
    Prop :=
  finiteAbelianNormSubgroup K L ≤ H

end Langlands.NYLL.LocalClassFieldTheory
