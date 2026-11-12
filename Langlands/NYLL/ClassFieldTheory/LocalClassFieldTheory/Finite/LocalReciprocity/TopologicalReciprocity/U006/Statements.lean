/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

/-
Modifications by Worker 120, 11 November 2026: extract the M257.006–008
signatures from Nyll/ClassFieldTheory/LocalClassFieldTheory/Finite/
LocalReciprocity/TopologicalReciprocity.lean at
fbd320cd8b1b06487c58227e92eb135794267709. Replace the theorems with
Prop-valued Statement targets, name the source-private theorem d006Statement,
prefix namespaces with Langlands.NYLL, and use focused published/Mathlib
imports. Preserve all Type-zero parameters, binder order and hypotheses.
Restore the published M257.001 topology instance locally.
LICENSE and NOTICE are retained in licenses/NYLL/.
-/

import Langlands.NYLL.ClassFieldTheory.LocalClassFieldTheory.Finite.LocalReciprocity.TopologicalReciprocity.U001.Definitions
import Mathlib.NumberTheory.LocalField.Basic
import Mathlib.Analysis.Normed.Module.FiniteDimension
import Mathlib.FieldTheory.Galois.Basic
import Mathlib.RingTheory.Valuation.Extension
import Mathlib.RingTheory.IntegralClosure.IsIntegralClosure.Defs

/-! # Targets for openness of local norm subgroups and discreteness of their quotients -/

open scoped ValuativeRel
open Langlands.NYLL.LocalFieldTheory

attribute [local instance] Langlands.NYLL.PortInternal.M257.d001

namespace Langlands.NYLL.PortInternal.M257

/-- Target for norm-subgroup openness with compatible local-field structures. -/
def d006Statement
    (K L : Type)
    [NontriviallyNormedField K] [NormedField L] [NormedAlgebra K L]
    [CompleteSpace K]
    [ValuativeRel K] [IsNonarchimedeanLocalField K]
    [ValuativeRel L] [IsNonarchimedeanLocalField L]
    [FiniteDimensional K L] [IsGalois K L]
    [Valuation.HasExtension (ValuativeRel.valuation K)
      (ValuativeRel.valuation L)]
    [IsIntegralClosure 𝒪[L] 𝒪[K] L] : Prop :=
  IsOpen (localNormSubgroup K L : Set Kˣ)

end Langlands.NYLL.PortInternal.M257

namespace Langlands.NYLL.LocalClassFieldTheory

/-- Target for norm-subgroup openness in the native base-field unit topology. -/
def localNormSubgroup_isOpenStatement
    (K L : Type) [Field K] [Field L] [Algebra K L]
    [FiniteDimensional K L] [IsGalois K L]
    [ValuativeRel K] [TopologicalSpace K]
    [IsNonarchimedeanLocalField K] : Prop :=
  IsOpen (localNormSubgroup K L : Set Kˣ)

/-- Target for discreteness of the native norm-quotient topology. -/
def normQuotient_discreteStatement
    (K L : Type) [Field K] [Field L] [Algebra K L]
    [FiniteDimensional K L] [IsGalois K L]
    [ValuativeRel K] [TopologicalSpace K]
    [IsNonarchimedeanLocalField K] : Prop :=
  DiscreteTopology (NormQuotient K L)

end Langlands.NYLL.LocalClassFieldTheory
