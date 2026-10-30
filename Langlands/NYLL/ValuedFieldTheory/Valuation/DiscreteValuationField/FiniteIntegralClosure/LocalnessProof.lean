/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)

Modifications by Worker 1045 (2026-10-29): adapt M245.006
(FiniteIntegralClosure.lean, lines 176-251) from upstream commit
fbd320cd8b1b06487c58227e92eb135794267709 to its published closed target,
with independent universe parameters u, v, w and the Langlands.NYLL prefix;
expand base.valuationSubring and base.maximalIdeal to the actual valuation
subring and its maximal ideal. Use the accepted M245.005 fiber theorem and
Mathlib's prime-to-fiber order isomorphism. Obtain a maximal ideal from the
nontriviality of the integral closure instead of integral lies-over, so the
faithful scalar action of the source proof is not needed, and show directly
that any two maximal ideals agree, using the current Mathlib lemma
Ideal.isMaximal_under_of_isIntegral_of_isMaximal. Replace upstream imports by
published dependencies and focused Mathlib imports. The retained license and
notices are in licenses/NYLL/.
-/

import Langlands.NYLL.ValuedFieldTheory.Valuation.DiscreteValuationField.FiniteIntegralClosure.LocalnessStatements
import Langlands.NYLL.ValuedFieldTheory.Valuation.DiscreteValuationField.FiniteIntegralClosure.FiberSubsingletonProof
import Mathlib.RingTheory.Ideal.GoingUp
import Mathlib.RingTheory.LocalRing.MaximalIdeal.Basic
import Mathlib.RingTheory.Spectrum.Maximal.Basic

/-!
# Localness of the finite integral closure

The only theorem proves NYLL M245.006 as its exact published closed
proposition.
-/

namespace Langlands.NYLL.ValuationTheory.DiscreteValuationField.ValuedExtension

/-- The actual integral closure of the valuation subring of a complete DVF in a
finite separable extension is a local ring (M245.006). -/
theorem integralClosure_isLocalRing_of_finite_separable.{u, v, w} :
    IntegralClosureIsLocalRingOfFiniteSeparableStatement.{u, v, w} := by
  intro K L _ _ _ _ base _
  let A := base.valuation.valuationSubring
  let B := integralClosure A L
  let m := IsLocalRing.maximalIdeal A
  have : Subsingleton (PrimeSpectrum (m.Fiber B)) :=
    integralClosure_base_maximal_fiber_subsingleton_of_finite_separable.{u, v, w} K L base
  have hover (M : MaximalSpectrum B) : M.asIdeal ∈ m.primesOver B :=
    ⟨M.isMaximal.isPrime, ⟨(IsLocalRing.eq_maximalIdeal
      (Ideal.isMaximal_under_of_isIntegral_of_isMaximal (R := A) M.asIdeal)).symm⟩⟩
  have : Subsingleton (MaximalSpectrum B) := by
    constructor
    intro M N
    let e := PrimeSpectrum.primesOverOrderIsoFiber A B m
    have h := e.injective
      (Subsingleton.elim (e ⟨M.asIdeal, hover M⟩) (e ⟨N.asIdeal, hover N⟩))
    exact MaximalSpectrum.ext (congrArg Subtype.val h)
  exact IsLocalRing.of_singleton_maximalSpectrum

end Langlands.NYLL.ValuationTheory.DiscreteValuationField.ValuedExtension
