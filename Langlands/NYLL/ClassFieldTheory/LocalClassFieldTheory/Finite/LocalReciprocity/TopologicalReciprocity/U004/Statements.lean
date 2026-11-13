/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

/-
Modifications by Worker 25, 13 November 2026: extract the M257.004–005
signatures from Nyll/ClassFieldTheory/LocalClassFieldTheory/Finite/
LocalReciprocity/TopologicalReciprocity.lean at
fbd320cd8b1b06487c58227e92eb135794267709. Replace the two source-private
theorems by Prop-valued targets d004Statement and d005Statement in
Langlands.NYLL.PortInternal.M257, remove their proofs, qualify references
to their published names and use focused published/Mathlib imports.
Preserve the common universe u, binder order and all hypotheses.
LICENSE and NOTICE are retained in licenses/NYLL/.
-/

import Langlands.NYLL.ClassFieldTheory.LocalClassFieldTheory.Finite.LocalReciprocity.TopologicalReciprocity.U002.Definitions
import Langlands.NYLL.ValuedFieldTheory.LocalField.NonarchimedeanLocalField.NormQuotient.U001.Definitions
import Langlands.NYLL.ValuedFieldTheory.LocalField.NonarchimedeanLocalField.UnitTopology.U001.Definitions
import Mathlib.Analysis.Normed.Module.FiniteDimension
import Mathlib.NumberTheory.LocalField.Basic
import Mathlib.FieldTheory.Separable
import Mathlib.RingTheory.Valuation.Extension
import Mathlib.RingTheory.IntegralClosure.IsIntegralClosure.Defs

/-! # Targets for compactness and intersection description of integer-unit norms -/

universe u

open scoped ValuativeRel

namespace Langlands.NYLL.PortInternal.M257

/-- Target: the norm image of valuation-ring units is compact. -/
def d004Statement
    (K L : Type u) [NontriviallyNormedField K] [NormedField L]
    [NormedAlgebra K L] [FiniteDimensional K L] [CompleteSpace K]
    [ValuativeRel L] [CompactSpace 𝒪[L]] : Prop :=
  IsCompact (d003 K L : Set Kˣ)

/-- Target: the integer-unit norm subgroup is the intersection of the norm
subgroup with the base valuation-ring units. -/
def d005Statement
    (K L : Type u)
    [Field K] [ValuativeRel K] [TopologicalSpace K]
    [_root_.IsNonarchimedeanLocalField K]
    [Field L] [ValuativeRel L] [TopologicalSpace L]
    [_root_.IsNonarchimedeanLocalField L]
    [Algebra K L] [FiniteDimensional K L] [Algebra.IsSeparable K L]
    [Valuation.HasExtension (ValuativeRel.valuation K)
      (ValuativeRel.valuation L)]
    [IsIntegralClosure 𝒪[L] 𝒪[K] L] : Prop :=
  d003 K L =
    Langlands.NYLL.LocalFieldTheory.localNormSubgroup K L ⊓
      Langlands.NYLL.LocalFieldTheory.localBaseUnitSubgroup K

end Langlands.NYLL.PortInternal.M257
