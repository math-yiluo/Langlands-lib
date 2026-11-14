/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import Langlands.NYLL.ClassFieldTheory.LocalClassFieldTheory.Finite.Existence.NormSubgroupOrderEmbedding.AbsoluteBase.Statements
import Langlands.NYLL.ClassFieldTheory.LocalClassFieldTheory.Finite.LocalReciprocity.GaloisExtensionQuotient.Initial.U001.Proofs

/-!
# NYLL M300.001: finiteness over the absolute base

Adapted by Worker 665 from NYLL commit
`fbd320cd8b1b06487c58227e92eb135794267709`, M300.001.
The source's finite-index transitivity argument is replaced by transport
along the published equality of the two base subgroups.
See the paired Markdown for provenance and the modification record.
Original license and notices: `licenses/NYLL/LICENSE` and `licenses/NYLL/NOTICE`.
-/

namespace Langlands.NYLL.LocalClassFieldTheory

open ClassFormation

/-- Finiteness over the concrete ground-field fixing group implies
finiteness over the abstract class-formation `baseField`. -/
theorem finiteAbelianSubextension_finite_over_absoluteBase
    (K : Type) [Field K]
    (L : FiniteAbelianSubextension (intrinsicAbstractBase K)) :
    finiteAbelianSubextension_finite_over_absoluteBaseStatement K L := by
  have hbase : intrinsicAbstractBase K =
      baseField (intrinsicAbsoluteGalois K) :=
    closedFixingSubgroup_bot_eq_baseField K (SeparableClosure K)
  change Finite ((baseField (intrinsicAbsoluteGalois K)).toSubgroup ⧸
    L.field.toSubgroup.subgroupOf
      (baseField (intrinsicAbsoluteGalois K)).toSubgroup)
  rw [← hbase]
  exact L.finite

end Langlands.NYLL.LocalClassFieldTheory
