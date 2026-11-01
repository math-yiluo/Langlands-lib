/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

/- Modifications by Worker 1199 (2026-11-01): extract the statement of
   M248.011 from upstream commit fbd320cd8b1b06487c58227e92eb135794267709,
   omit its proof, and close its Type 0 field/algebra/local-base telescope
   inside a Prop-valued definition. Expand M196.001
   ValuedExtension.HasUniqueValuationExtension at universes 0, 0, 0, 0, y,
   keeping the arbitrary comparison universe y and the published named chosen
   target. Prefix the namespace with Langlands.NYLL, write
   Valuation.HasExtension in prefix form, and replace the original imports by
   the published chosen-data module and Mathlib's valuation-extension module.
   The original LICENSE and NOTICE are retained in licenses/NYLL/. -/

import Mathlib.RingTheory.Valuation.Extension
import Langlands.NYLL.ValuedFieldTheory.LocalField.NonarchimedeanLocalField.FiniteExtensionCompleteDVF.Chosen

/-!
# Uniqueness of the chosen valuation on a finite local extension: statement

Every valuation extending the canonical base valuation is equivalent to the
named chosen valuation on the finite separable extension. The comparison
value group may lie in any universe.
-/

namespace Langlands.NYLL.LocalFieldTheory

universe y

/-- Every valuation extending the canonical valuation of a nonarchimedean
local field to a finite separable extension is equivalent to the named chosen
valuation, with an arbitrary comparison value-group universe. -/
def ChosenLocalExtensionUniqueValuationExtensionStatement : Prop :=
  ∀ (K L : Type) [Field K] [Field L] [Algebra K L]
    [FiniteDimensional K L] [Algebra.IsSeparable K L]
    [ValuativeRel K] [TopologicalSpace K]
    [IsNonarchimedeanLocalField K],
    ∀ {Gamma' : Type y} [LinearOrderedCommGroupWithZero Gamma']
      (v' : _root_.Valuation L Gamma')
      [_root_.Valuation.HasExtension (localCompleteDVF K).valuation v'],
      (chosenLocalExtensionCompleteDVF K L).valuation.IsEquiv v'

end Langlands.NYLL.LocalFieldTheory
