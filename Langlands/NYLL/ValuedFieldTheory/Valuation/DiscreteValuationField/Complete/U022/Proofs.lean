/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import Langlands.NYLL.ValuedFieldTheory.Valuation.DiscreteValuationField.Complete.Statements

/-!
# NYLL M107.022: a complete discrete valuation field admits a uniformizer

Modified by Worker 5264, 15 November 2026: prove the published target
`CompleteDVF.exists_uniformizerStatement` (M107.022) following the source
proof of `CompleteDVF.exists_uniformizer` in
`Nyll/ValuedFieldTheory/Valuation/DiscreteValuationField/Complete.lean`
at fbd320cd8b1b06487c58227e92eb135794267709. Prefix the namespace with
`Langlands.NYLL`, give the theorem the published proposition as its type,
begin the proof with `show` stating it unfolded, replace the source term
`F.toDVF.exists_uniformizer` (the unpublished M103.020) by its own source
body, a `change` to the valuation subring of `F.valuation` followed by the
Mathlib theorem `Valuation.exists_isUniformizer_of_isCyclic_of_nontrivial`,
replace the source imports by the published statement module and omit the universe
`w` and the rest of the source file. See the paired Markdown and
`licenses/NYLL/LICENSE` and `licenses/NYLL/NOTICE`.
-/

namespace Langlands.NYLL.ValuationTheory

noncomputable section

universe u v

namespace DiscreteValuationField

namespace CompleteDVF

variable {K : Type u} [Field K]

/-- A complete discrete valuation field admits a uniformizer. -/
theorem exists_uniformizer (F : CompleteDVF.{u, v} K) :
    exists_uniformizerStatement F := by
  show Exists (fun pi : F.valuationSubring => F.valuation.IsUniformizer (pi : K))
  change Exists
    (fun pi : F.valuation.valuationSubring => F.valuation.IsUniformizer (pi : K))
  exact _root_.Valuation.exists_isUniformizer_of_isCyclic_of_nontrivial F.valuation

end CompleteDVF

end DiscreteValuationField

end

end Langlands.NYLL.ValuationTheory
