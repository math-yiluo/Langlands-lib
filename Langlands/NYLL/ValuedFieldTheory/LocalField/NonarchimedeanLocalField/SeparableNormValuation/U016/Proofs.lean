/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

/-
Modifications by Worker 173, 13 November 2026:
Extract the proof of M162.016 from
Nyll/ValuedFieldTheory/LocalField/NonarchimedeanLocalField/SeparableNormValuation.lean
at fbd320cd8b1b06487c58227e92eb135794267709 (lines 321 and 389-410).
Prefix the namespace with Langlands.NYLL, give the theorem the published
statement relNorm_maximalIdeal_eq_pow_residue_finrankStatement K L as its
type, and import only the U016 Statements module and the published U012 and
U015 proof modules. The file-level local instance attribute on
FractionRing.liftAlgebra is kept. Because the imported M162.012 theorem now
has the statement constant relNorm_eq_pow_inertiaDeg_of_isSeparableStatement
as its type, the rewrite at h first unfolds that constant; the other proof
steps are unchanged. All other source declarations are omitted. The upstream
LICENSE and NOTICE are preserved in licenses/NYLL/.
-/

import Langlands.NYLL.ValuedFieldTheory.LocalField.NonarchimedeanLocalField.SeparableNormValuation.U016.Statements
import Langlands.NYLL.ValuedFieldTheory.LocalField.NonarchimedeanLocalField.SeparableNormValuation.U012.Proofs
import Langlands.NYLL.ValuedFieldTheory.LocalField.NonarchimedeanLocalField.SeparableNormValuation.U015.Proofs

/-!
# Relative norm of the maximal ideal of a local-field extension

For a finite separable extension `L / K` of nonarchimedean local fields whose
valuation integer rings form a finite extension, the relative ideal norm of
the maximal ideal of `𝒪[L]` is the maximal ideal of `𝒪[K]` raised to the
residue degree `[𝓀[L] : 𝓀[K]]`.
-/

namespace Langlands.NYLL.LocalClassFieldTheory

noncomputable section

universe u v

open scoped ValuativeRel

attribute [local instance] FractionRing.liftAlgebra

/-- In a finite separable local-field extension, the relative ideal norm of
the upstairs maximal ideal is the residue-degree power of the base maximal
ideal. -/
theorem relNorm_maximalIdeal_eq_pow_residue_finrank
    (K : Type u) (L : Type v)
    [Field K] [ValuativeRel K] [TopologicalSpace K]
    [IsNonarchimedeanLocalField K]
    [Field L] [ValuativeRel L] [TopologicalSpace L]
    [IsNonarchimedeanLocalField L]
    [Algebra K L] [FiniteDimensional K L] [Algebra.IsSeparable K L]
    [Valuation.HasExtension (ValuativeRel.valuation K)
      (ValuativeRel.valuation L)]
    [Module.Finite 𝒪[K] 𝒪[L]] :
    relNorm_maximalIdeal_eq_pow_residue_finrankStatement K L := by
  let : Algebra.IsSeparable (FractionRing 𝒪[K]) (FractionRing 𝒪[L]) :=
    fractionRing_integerRing_isSeparable K L
  have h := relNorm_eq_pow_inertiaDeg_of_isSeparable
    𝒪[K] 𝒪[L] (𝓂[L] : Ideal 𝒪[L]) (𝓂[K] : Ideal 𝒪[K])
  rw [relNorm_eq_pow_inertiaDeg_of_isSeparableStatement,
    Ideal.inertiaDeg_eq_of_isMaximal
    (𝓂[K] : Ideal 𝒪[K]) (𝓂[L] : Ideal 𝒪[L])] at h
  exact h

end

end Langlands.NYLL.LocalClassFieldTheory
