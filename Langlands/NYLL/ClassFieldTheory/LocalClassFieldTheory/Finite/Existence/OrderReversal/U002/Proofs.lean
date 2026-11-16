/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

/-
Modified by Worker 546, 16 November 2026: extract the proof of M402.002
from OrderReversal.lean, lines 64–81, at upstream commit
fbd320cd8b1b06487c58227e92eb135794267709. Prefix the namespace with
Langlands.NYLL, import the published proposition and focused proof dependencies,
and state the theorem with the exact closed Statement as its type. Introduce
the complete original telescope in the proof; the remaining proof is unchanged.
Remove unused namespace openings. See the paired Markdown for the source map.
The original LICENSE and NOTICE remain in licenses/NYLL/.
-/

import Langlands.NYLL.ClassFieldTheory.LocalClassFieldTheory.Finite.Existence.OrderReversal.U002.Statements
import Langlands.NYLL.ClassFieldTheory.LocalClassFieldTheory.Finite.LocalReciprocity.SeparableUnitsNorm.Embedding.U013.Proofs
import Langlands.NYLL.ClassFieldTheory.LocalClassFieldTheory.Finite.LocalReciprocity.SeparableUnitsNorm.BaseUnits.NormSubgroup.U007.Proofs

/-!
# Norm transport for an embedded finite abelian extension

Proof of the published M402.002 proposition, following the field-range
transport argument in the pinned NYLL source.
-/

noncomputable section

namespace Langlands.NYLL.LocalClassFieldTheory

open CyclicCohomology

/-- Under the canonical identification of the abstract base fixed units with
`Kˣ`, the abstract norm subgroup of an embedded finite abelian extension is
its ordinary field-norm subgroup. -/
theorem map_finiteAbelianAbstractExtension_normSubgroup_eq :
    map_finiteAbelianAbstractExtension_normSubgroup_eqStatement := by
  intro K L _ _ _ _ _ i
  let : FiniteDimensional K (AlgHom.fieldRange i) :=
    (AlgEquiv.ofInjectiveField i).toLinearEquiv.finiteDimensional
  let : IsGalois K (AlgHom.fieldRange i) :=
    IsGalois.of_algEquiv (AlgEquiv.ofInjectiveField i)
  rw [show additiveNormSubgroup K L =
      additiveNormSubgroup K (AlgHom.fieldRange i) by
    exact congrArg Subgroup.toAddSubgroup
      (localNormSubgroup_fieldRange_eq K (SeparableClosure K) L i).symm]
  exact map_finiteNormSubgroup_eq_additiveNormSubgroup K
    (SeparableClosure K) (AlgHom.fieldRange i)

end Langlands.NYLL.LocalClassFieldTheory

end
