/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)

Modifications by Worker 1045 (2026-10-30): adapt M245.008
(FiniteIntegralClosure.lean, lines 263-289) and M245.009 (lines 291-305,
including the omit clause at line 293) from upstream commit
fbd320cd8b1b06487c58227e92eb135794267709 to their published closed targets,
with independent universe parameters u, v, w and the Langlands.NYLL prefix;
expand base.valuationSubring and base.maximalIdeal to the actual valuation
subring and its maximal ideal. Prove the injectivity of the canonical map
(M245.001, lines 33-47) privately, without its FaithfulSMul wrapper
(M245.002); obtain that the base maximal ideal is nonzero from Mathlib's
Valuation.valuationSubring_not_isField instead of the NYLL theorem
CompleteDVF.maximalIdeal_ne_bot (Complete.lean); use the published M245.006
theorem and the current Mathlib lemma IsLocalRing.map_maximalIdeal_le in
place of IsLocalRing.local_hom_TFAE. Replace upstream imports by published
dependencies and focused Mathlib imports. The retained license and notices
are in licenses/NYLL/.
-/

import Langlands.NYLL.ValuedFieldTheory.Valuation.DiscreteValuationField.FiniteIntegralClosure.IdealImageStatements
import Mathlib.RingTheory.IntegralClosure.IsIntegralClosure.Basic
import Mathlib.RingTheory.LocalRing.RingHom.Basic

/-!
# Images of the base maximal ideal in a finite integral closure

The two public theorems prove NYLL M245.008 and M245.009 as their exact
published closed propositions. The injectivity of the canonical map and the
nonvanishing of the base maximal ideal are private auxiliary facts.
-/

namespace Langlands.NYLL.ValuationTheory.DiscreteValuationField.ValuedExtension

/-- The canonical map from the valuation subring into the integral closure is
injective, since its composite into `L` is the inclusion into `K` followed by
the field map `K → L` (M245.001). -/
private theorem algebraMap_valuationSubring_integralClosure_injective.{u, v, w}
    (K : Type u) (L : Type w) [Field K] [Field L] [Algebra K L]
    (base : CompleteDVF.{u, v} K) :
    Function.Injective
      (algebraMap base.valuation.valuationSubring
        (integralClosure base.valuation.valuationSubring L)) := by
  intro x y hxy
  apply Subtype.ext
  apply (algebraMap K L).injective
  exact congrArg
    (fun z : integralClosure base.valuation.valuationSubring L => (z : L)) hxy

/-- The maximal ideal of the valuation subring of a complete DVF is nonzero,
because the valuation subring of a rank-one discrete valuation is not a
field. -/
private theorem valuationSubring_maximalIdeal_ne_bot.{u, v}
    {K : Type u} [Field K] (base : CompleteDVF.{u, v} K) :
    IsLocalRing.maximalIdeal base.valuation.valuationSubring ≠ ⊥ :=
  Ring.ne_bot_of_isMaximal_of_not_isField (IsLocalRing.maximalIdeal.isMaximal _)
    (Valuation.valuationSubring_not_isField base.valuation)

/-- In a finite separable extension, the ideal generated in the actual integral
closure by the base maximal ideal lies in the canonical maximal ideal
(M245.008). -/
theorem integralClosure_base_maximal_map_le_maximalIdeal_of_finite_separable.{u, v, w} :
    IntegralClosureBaseMaximalMapLeMaximalIdealOfFiniteSeparableStatement.{u, v, w} := by
  intro K L _ _ _ _ base _
  let A := base.valuation.valuationSubring
  let B := integralClosure A L
  let : IsLocalRing B :=
    integralClosure_isLocalRing_of_finite_separable.{u, v, w} K L base
  change (IsLocalRing.maximalIdeal A).map (algebraMap A B) ≤ IsLocalRing.maximalIdeal B
  have : IsLocalHom (algebraMap A B) :=
    (algebraMap_isIntegral_iff.mpr (inferInstance : Algebra.IsIntegral A B)).isLocalHom
      (algebraMap_valuationSubring_integralClosure_injective.{u, v, w} K L base)
  exact IsLocalRing.map_maximalIdeal_le (algebraMap A B)

/-- In a separable algebraic extension, finite or not, the ideal generated in the
actual integral closure by the base maximal ideal is nonzero (M245.009). -/
theorem integralClosure_base_maximal_map_ne_bot_of_finite_separable.{u, v, w} :
    IntegralClosureBaseMaximalMapNeBotOfFiniteSeparableStatement.{u, v, w} := by
  intro K L _ _ _ base _ hbot
  exact valuationSubring_maximalIdeal_ne_bot base
    ((Ideal.map_eq_bot_iff_of_injective
      (algebraMap_valuationSubring_integralClosure_injective.{u, v, w} K L base)).1 hbot)

end Langlands.NYLL.ValuationTheory.DiscreteValuationField.ValuedExtension
