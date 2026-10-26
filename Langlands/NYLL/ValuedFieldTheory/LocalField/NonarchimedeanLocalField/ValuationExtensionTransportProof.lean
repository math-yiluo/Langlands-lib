/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)

Adapted by Worker 586 from ClassFieldTheory commit
fbd320cd8b1b06487c58227e92eb135794267709, ShrinkTransport.lean,
hasExtension_comap_ringEquivs and hasExtension_of_isEquiv:
prefix the namespace with Langlands.NYLL, import the published statement
module, and introduce the full universally quantified targets explicitly.
The original proof routes are retained. See licenses/NYLL/LICENSE and
licenses/NYLL/NOTICE.
-/

import Langlands.NYLL.ValuedFieldTheory.LocalField.NonarchimedeanLocalField.ValuationExtensionTransportStatement

/-!
# Generic valuation-extension transport: proofs

These theorems prove the complete published propositions, including their
independent universes and the ring/monoid scope of equivalent replacement.
-/

namespace Langlands.NYLL.LocalFieldTheory

/-- Compatible field equivalences preserve the valuation-extension relation. -/
theorem hasExtension_comap_ringEquivs :
    hasExtension_comap_ringEquivsStatement := by
  intro F G F₀ G₀ _ _ _ _ _ _ ΓF ΓG _ _ eF eG h vF vG _
  constructor
  rw [Valuation.isEquiv_iff_val_le_one]
  intro a
  change vF (eF a) ≤ 1 ↔ vG (eG (algebraMap F₀ G₀ a)) ≤ 1
  rw [h]
  exact (Valuation.HasExtension.val_map_le_one_iff vF vG (eF a)).symm

/-- Equivalent valuations may replace both valuations in an extension relation. -/
theorem hasExtension_of_isEquiv :
    hasExtension_of_isEquivStatement := by
  intro F G _ _ _ ΓF ΓF' ΓG ΓG' _ _ _ _ vF vF' vG vG' _ hF hG
  constructor
  intro x y
  have hext : vF.IsEquiv (vG.comap (algebraMap F G)) :=
    Valuation.HasExtension.val_isEquiv_comap
  exact (hF.symm x y).trans
    ((hext x y).trans
      (hG (algebraMap F G x) (algebraMap F G y)))

end Langlands.NYLL.LocalFieldTheory
