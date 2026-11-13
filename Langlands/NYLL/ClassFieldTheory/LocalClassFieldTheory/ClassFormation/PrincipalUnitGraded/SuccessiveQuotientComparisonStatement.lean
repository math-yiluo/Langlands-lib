/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import Langlands.NYLL.GaloisCohomology.Cyclic.Herbrand.NormalBasisLattice.U102.Definitions
import Langlands.NYLL.GaloisCohomology.Cyclic.Herbrand.NormalBasisLattice.U108.Definitions
import Langlands.NYLL.ValuedFieldTheory.LocalField.NonarchimedeanLocalField.PrincipalUnits.Definitions

/-!
Worker 197: adapted M153.005 from NYLL fbd320cd8b1b06487c58227e92eb135794267709.
The source theorem target becomes a Prop-valued definition with the complete
source telescope. Namespace and imports are adapted; the target is unchanged.
See the paired Markdown and licenses/NYLL/.
-/

namespace Langlands.NYLL.LocalClassFieldTheory

noncomputable section

universe u
open CyclicCohomology LocalFieldTheory
open scoped ValuativeRel
open IsNonarchimedeanLocalField

set_option linter.unusedVariables false in
def exists_chosenNormalBasisPrincipalUnitSuccQuotMulEquivLatticeSuccQuotStatement
    (K L : Type u)
    [Field K]
    [Field L]
    [Algebra K L]
    [FiniteDimensional K L]
    [IsGalois K L]
    [ValuativeRel K]
    [TopologicalSpace K]
    [IsNonarchimedeanLocalField K]
    [ValuativeRel L]
    [Valuation.HasExtension (ValuativeRel.valuation K) (ValuativeRel.valuation L)]
    [TopologicalSpace L] [IsNonarchimedeanLocalField L]
    [Module.Finite 𝒪[K] 𝒪[L]] : Prop :=
  ∃ c : Nat, ∀ n : Nat, c ≤ n →
    ∃ Vn Vsucc : Subgroup 𝒪[L]ˣ,
      ∃ hV : Vsucc ≤ Vn,
        ∃ hVn : (Vn : Set 𝒪[L]ˣ) = chosenNormalBasisPrincipalUnitSet K L n,
          (Vsucc : Set 𝒪[L]ˣ) = chosenNormalBasisPrincipalUnitSet K L (n + 1) ∧
            ∃ Φ : chosenNormalBasisPrincipalUnitSuccQuot (L := L) hV ≃*
                Multiplicative (chosenNormalBasisLatticeSuccQuot K L n),
              Vn ≤ principalUnits L 1 ∧
                ∀ u : Vn,
                  Φ (chosenNormalBasisPrincipalUnitSuccQuotMk (L := L) hV u) =
                    Multiplicative.ofAdd
                      (chosenNormalBasisPrincipalUnitLatticeClass K L n
                        (u : 𝒪[L]ˣ) (by exact hVn ▸ u.2))

end

end Langlands.NYLL.LocalClassFieldTheory
