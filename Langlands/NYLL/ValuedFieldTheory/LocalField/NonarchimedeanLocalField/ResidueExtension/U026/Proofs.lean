/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

/-
Modifications by Worker 395, 14 November 2026 UTC:
Extract only the proof of M138.026
(integerRing_moduleFinite_of_isIntegralClosure) from
Nyll/ValuedFieldTheory/LocalField/NonarchimedeanLocalField/ResidueExtension.lean
at fbd320cd8b1b06487c58227e92eb135794267709. Add the Langlands.NYLL
namespace prefix; import the published ResidueExtension
ModuleFiniteStatement module and, of the original imports, only
Mathlib.RingTheory.DedekindDomain.IntegralClosure, which provides
IsIntegralClosure.finite. Keep the noncomputable section, `universe u`,
`open scoped ValuativeRel` and the docstring, and state the theorem as the
published Statement applied to the source parameters. The proof is
unchanged. The original LICENSE and NOTICE are retained in licenses/NYLL/.
-/

import Mathlib.RingTheory.DedekindDomain.IntegralClosure
import Langlands.NYLL.ValuedFieldTheory.LocalField.NonarchimedeanLocalField.ResidueExtension.ModuleFiniteStatement

/-!
# Finiteness of integer rings from integral closure

The proof that, for a finite separable extension of a nonarchimedean local
field whose valuation ring is the integral closure of the base valuation
ring, the extension valuation ring is a finite module over the base one.
-/

namespace Langlands.NYLL.LocalFieldTheory

noncomputable section

universe u

open scoped ValuativeRel

/-- Finite separable extensions whose valuation ring is the integral closure of
the base valuation ring give a finite module extension of valuation integer
rings. -/
theorem integerRing_moduleFinite_of_isIntegralClosure (K L : Type u)
    [Field K] [ValuativeRel K] [TopologicalSpace K] [IsNonarchimedeanLocalField K]
    [Field L] [ValuativeRel L] [Algebra K L] [FiniteDimensional K L]
    [Algebra.IsSeparable K L]
    [Valuation.HasExtension (ValuativeRel.valuation K) (ValuativeRel.valuation L)]
    [IsIntegralClosure 𝒪[L] 𝒪[K] L] :
    integerRing_moduleFinite_of_isIntegralClosureStatement K L :=
  IsIntegralClosure.finite 𝒪[K] K L 𝒪[L]

end

end Langlands.NYLL.LocalFieldTheory
