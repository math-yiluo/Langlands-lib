/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)

Modifications by Worker 384 (2026-10-31): adapt only the proof of M245.017
(FiniteIntegralClosure.lean, lines 513-629, ambient lines 23 and 30-31)
from upstream commit fbd320cd8b1b06487c58227e92eb135794267709.
Prove its unchanged published closed target in Langlands.NYLL, retaining
independent universes u, v, w. Expand base.valuationSubring, apply the
published closed localness, DVR, maximal-ideal completeness and
universe-general linear-equivalence completeness theorems explicitly,
and unfold the canonical maximal ideal to match its localness witness.
Use Mathlib's current IsAdicComplete.map_algebraMap_iff spelling and
explicit module argument.
Replace upstream imports by the published target/proofs and a focused
Mathlib standard-valuation import. Retain the original valuation,
ring equivalence, maximal-ideal image and pointwise membership proof.
The retained license and notices are in licenses/NYLL/.
-/

import Langlands.NYLL.ValuedFieldTheory.Valuation.DiscreteValuationField.FiniteIntegralClosure.StandardCompleteDVFStatement
import Langlands.NYLL.ValuedFieldTheory.Valuation.DiscreteValuationField.FiniteIntegralClosure.DVRProof
import Langlands.NYLL.ValuedFieldTheory.Valuation.DiscreteValuationField.FiniteIntegralClosure.MaximalIdealCompletenessProof
import Langlands.NYLL.ValuedFieldTheory.Valuation.DiscreteValuationField.HenselianFinite.CompletenessProofs
import Mathlib.RingTheory.Valuation.Discrete.IsDiscreteValuationRing

/-!
# Actual integral-closure standard complete-DVF existence

The standard valuation of the actual integral closure supplies the same
complete-DVF witness for both the pointwise membership comparison and
the ring-equivalence conclusion of NYLL M245.017.
-/

namespace Langlands.NYLL.ValuationTheory.DiscreteValuationField.ValuedExtension

/-- The actual integral closure in a finite separable extension supplies a
complete discrete valuation with value group in `Type 0`, the exact
pointwise integral-closure comparison and the corresponding ring equivalence
(M245.017), with precisely the published closed target. -/
theorem exists_integralClosure_standard_completeDVF.{u, v, w} :
    ExistsIntegralClosureStandardCompleteDVFStatement.{u, v, w} := by
  intro K L _ _ _ _ base _
  classical
  let B := integralClosure base.valuation.valuationSubring L
  let : IsLocalRing B :=
    integralClosure_isLocalRing_of_finite_separable.{u, v, w} K L base
  let : IsDomain B := by
    change IsDomain (integralClosure base.valuation.valuationSubring L)
    infer_instance
  let : IsDiscreteValuationRing B :=
    integralClosure_isDiscreteValuationRing_of_finite_separable.{u, v, w} K L base
  let : IsFractionRing B L := by
    change IsFractionRing (integralClosure base.valuation.valuationSubring L) L
    exact integralClosure.isFractionRing_of_finite_extension K L
  let vL := (IsDiscreteValuationRing.maximalIdeal B).valuation L
  let e : B ≃+* vL.valuationSubring :=
    IsDiscreteValuationRing.equivValuationSubring (A := B) (K := L)
  let : Algebra B vL.valuationSubring := e.toRingHom.toAlgebra
  let eLin : B ≃ₗ[B] vL.valuationSubring :=
    { toFun := e
      invFun := e.symm
      left_inv := e.left_inv
      right_inv := e.right_inv
      map_add' := e.map_add
      map_smul' := by
        intro r x
        change e (r * x) = (algebraMap B vL.valuationSubring r) * e x
        simp [RingHom.algebraMap_toAlgebra] }
  let : IsAdicComplete (IsLocalRing.maximalIdeal B) B := by
    simpa only [CanonicalIntegralClosure.maximalIdeal] using
      integralClosure_maximalIdeal_isAdicComplete_of_finite_separable.{u, v, w} K L base
  have hcompleteAsB :
      IsAdicComplete (IsLocalRing.maximalIdeal B) vL.valuationSubring :=
    isAdicComplete_of_linearEquiv.{w, w, w} B B vL.valuationSubring
      (IsLocalRing.maximalIdeal B) eLin
  have hcompleteMap :
      IsAdicComplete
        ((IsLocalRing.maximalIdeal B).map
          (algebraMap B vL.valuationSubring))
        vL.valuationSubring :=
    (IsAdicComplete.map_algebraMap_iff
      (I := IsLocalRing.maximalIdeal B)
      (S := vL.valuationSubring) (M := vL.valuationSubring)).2 hcompleteAsB
  have hmem (x : B) :
      algebraMap B vL.valuationSubring x ∈
          IsLocalRing.maximalIdeal vL.valuationSubring ↔
        x ∈ IsLocalRing.maximalIdeal B := by
    simp only [IsLocalRing.mem_maximalIdeal, mem_nonunits_iff]
    constructor
    · intro hx hunit
      exact hx (hunit.map (algebraMap B vL.valuationSubring))
    · intro hx hunit
      apply hx
      have hpre := hunit.map e.symm.toRingHom
      simpa [RingHom.algebraMap_toAlgebra] using hpre
  have hmapMax :
      (IsLocalRing.maximalIdeal B).map
          (algebraMap B vL.valuationSubring) =
        IsLocalRing.maximalIdeal vL.valuationSubring := by
    apply le_antisymm
    · rw [Ideal.map_le_iff_le_comap]
      intro x hx
      exact (hmem x).2 hx
    · intro y hy
      have hx :
          e.symm y ∈ IsLocalRing.maximalIdeal B := by
        apply (hmem (e.symm y)).1
        simpa [RingHom.algebraMap_toAlgebra] using hy
      have hmap :=
        Ideal.mem_map_of_mem (algebraMap B vL.valuationSubring) hx
      simpa [RingHom.algebraMap_toAlgebra] using hmap
  have hcompletev :
      IsAdicComplete
        (IsLocalRing.maximalIdeal vL.valuationSubring)
        vL.valuationSubring := by
    simpa [hmapMax] using hcompleteMap
  have hmapSub :
      Subring.map (algebraMap B L) ⊤ =
        vL.valuationSubring.toSubring :=
    IsDiscreteValuationRing.map_algebraMap_eq_valuationSubring
      (A := B) (K := L)
  have hmemStandard (z : L) :
      z ∈ vL.valuationSubring ↔ z ∈ B.toSubring := by
    constructor
    · intro hz
      have hzmap :
          z ∈ Subring.map (algebraMap B L) ⊤ := by
        simpa [hmapSub] using hz
      rcases hzmap with ⟨b, _hbtop, hb⟩
      rw [← hb]
      exact b.2
    · intro hz
      have hzmap :
          z ∈ Subring.map (algebraMap B L) ⊤ :=
        ⟨⟨z, hz⟩, trivial, rfl⟩
      simpa [hmapSub] using hzmap
  let : Valuation.IsCompleteDiscrete vL :=
    { isRankOneDiscrete := inferInstance
      isAdicComplete := hcompletev }
  let target : CompleteDVF.{w, 0} L :=
    { ValueGroup := WithZero (Multiplicative ℤ)
      instValueGroup := inferInstance
      valuation := vL
      instCompleteDiscrete := inferInstance }
  refine ⟨target, ?_, e, trivial⟩
  intro z
  exact hmemStandard z

end Langlands.NYLL.ValuationTheory.DiscreteValuationField.ValuedExtension
