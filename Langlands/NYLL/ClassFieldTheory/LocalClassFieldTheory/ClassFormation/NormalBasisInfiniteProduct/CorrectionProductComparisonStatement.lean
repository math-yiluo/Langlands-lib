/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

-- Modified by Worker 197: extract M150.012 from NYLL fbd320cd,
-- prefix the namespace and narrow imports. See the paired Markdown.

import Langlands.NYLL.ClassFieldTheory.LocalClassFieldTheory.ClassFormation.NormalBasisInfiniteProduct.PrincipalUnitSequence
import Langlands.NYLL.ClassFieldTheory.LocalClassFieldTheory.ClassFormation.NormalBasisInfiniteProduct.CorrectionProduct
import Langlands.NYLL.ValuedFieldTheory.LocalField.NonarchimedeanLocalField.PrincipalUnitQuotients.CorrectionDefinitions

namespace Langlands.NYLL.LocalClassFieldTheory

noncomputable section

universe u
open CyclicCohomology LocalFieldTheory
open scoped ValuativeRel

/-- The normal-basis partial products are definitionally the standard
principal-unit correction products after the lattice-to-ideal bridge. -/
def chosenNormalBasisPrincipalUnitCorrectionProduct_eq_principalUnitsCorrectionProductStatement
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
    {b n : Nat}
    (hb : chosenBaseUniformizerPowSubmodule K L b
        (chosenNormalBasisIntegerLattice K L) ≤
      integerRingFieldSubmodule K L)
    (hbn : b + 1 ≤ n) (z : Nat → 𝒪[L]ˣ)
    (hz : ∀ i : Nat, z i ∈ chosenNormalBasisPrincipalUnitSet K L (n + i))
    (d : Nat) : Prop :=
  chosenNormalBasisPrincipalUnitCorrectionProduct (L := L) z d =
    principalUnitsCorrectionProduct L 1
      (chosenNormalBasisPrincipalUnitSequenceAsPrincipalUnits K L hb hbn z hz) d

end

end Langlands.NYLL.LocalClassFieldTheory
