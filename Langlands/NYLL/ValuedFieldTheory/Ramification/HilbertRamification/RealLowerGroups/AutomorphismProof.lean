/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)

Modified by Worker 1199, 2026-11-01, with the transport specialization
contributed by Worker 106: adapt M304.003 from upstream commit
fbd320cd8b1b06487c58227e92eb135794267709 to the published closed Prop,
prefix the namespace with Langlands.NYLL, and replace its M304.002 helper
by the published generic valuation-extension transport theorem.
Retained license and notices: licenses/NYLL/.
-/

import Langlands.NYLL.ValuedFieldTheory.Ramification.HilbertRamification.RealLowerGroups.AutomorphismStatement
import Langlands.NYLL.ValuedFieldTheory.LocalField.NonarchimedeanLocalField.ValuationExtensionTransportProof

/-!
# Valuation-ring preservation from unique extension: proof

This proves the complete published M304.003 target. Its original signature
occupies lines 70–76 and its proof lines 77–86 of `RealLowerGroups.lean`.
The extension instance for the pulled-back valuation is obtained by
specializing the published generic transport theorem.
-/

universe u v w x

namespace Langlands.NYLL.RamificationTheory.DiscreteValuationField.DVF

/-- Unique extension forces every supplied algebra automorphism to preserve
membership in the chosen target valuation subring. -/
theorem mem_valuationSubring_algEquiv_iff_of_hasUniqueValuationExtension :
    MemValuationSubringAlgEquivIffOfHasUniqueValuationExtensionStatement.{u, v, w, x} := by
  intro K L _ _ _ base target _ huniq σ z
  let vσ := target.valuation.comap (σ : L →+* L)
  let : base.valuation.HasExtension vσ := by
    have htransport :=
      Langlands.NYLL.LocalFieldTheory.hasExtension_comap_ringEquivs
        (RingEquiv.refl K) σ.toRingEquiv (fun a => σ.commutes a)
        base.valuation target.valuation
    change (base.valuation.comap (RingHom.id K)).HasExtension vσ at htransport
    simpa only [Valuation.comap_id] using htransport
  have hsub : target.valuation.valuationSubring = vσ.valuationSubring :=
    (Valuation.isEquiv_iff_valuationSubring target.valuation vσ).1 (huniq vσ)
  change z ∈ target.valuation.valuationSubring ↔ z ∈ vσ.valuationSubring
  rw [hsub]

end Langlands.NYLL.RamificationTheory.DiscreteValuationField.DVF
