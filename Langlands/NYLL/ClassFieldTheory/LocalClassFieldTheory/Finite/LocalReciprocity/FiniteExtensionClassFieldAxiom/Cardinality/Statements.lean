/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import Langlands.NYLL.ClassFieldTheory.LocalClassFieldTheory.Finite.LocalReciprocity.FiniteExtensionClassFieldAxiom.Cardinality.Definitions
import Mathlib.NumberTheory.LocalField.Basic

/-!
# Finite extension and tower unit Tate cardinality targets

Adapted by Worker 203 from NYLL commit
`fbd320cd8b1b06487c58227e92eb135794267709`.
See the paired Markdown for the declaration map and complete modification record.
The original license and notices are retained in `licenses/NYLL/LICENSE` and
`licenses/NYLL/NOTICE`.
-/

namespace Langlands.NYLL.LocalClassFieldTheory
noncomputable section
def finiteExtensionUnits_tate_card_of_generatorStatement
    (K L : Type) [Field K] [Field L] [Algebra K L]
    [FiniteDimensional K L] [IsGalois K L]
    [ValuativeRel K] [TopologicalSpace K] [IsNonarchimedeanLocalField K]
    (g : Gal(L/K))
    (hg : ∀ sigma : Gal(L / K), sigma ∈ Subgroup.zpowers g) : Prop :=
UnitsTateCardinalityData K L

def finiteTowerUnits_tate_card_of_generatorStatement
    (k K L : Type) [Field k] [Field K] [Field L]
    [Algebra k K] [FiniteDimensional k K]
    [Algebra K L] [FiniteDimensional K L] [IsGalois K L]
    [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
    (g : Gal(L/K))
    (hg : ∀ sigma : Gal(L / K), sigma ∈ Subgroup.zpowers g) : Prop :=
UnitsTateCardinalityData K L

end
end Langlands.NYLL.LocalClassFieldTheory
