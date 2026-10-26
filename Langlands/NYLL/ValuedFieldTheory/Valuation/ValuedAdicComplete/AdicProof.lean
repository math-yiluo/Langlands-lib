/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

/- Modifications by Worker 384 (2026-10-26): extract M247.002 alone, prove the
   published closed target in Langlands.NYLL, replace the M107.005 dependency
   with its Mathlib divisibility calculation as a local have, and use focused
   imports. Reuse Worker 25's P3 adaptation: install MulArchimedean locally on
   the explicit restricted value group required by the approved Mathlib API. -/

import Langlands.NYLL.ValuedFieldTheory.Valuation.ValuedAdicComplete.Statements
import Mathlib.RingTheory.Valuation.Discrete.RankOne
import Mathlib.GroupTheory.ArchimedeanDensely
import Mathlib.Topology.Algebra.Valued.ValuedField

/-!
# Native maximal-ideal adic topology

The actual valuation subring, with its native subtype topology from the supplied
`Valued` instance, has the powers of its maximal ideal as a basis of open
neighborhoods of zero.
-/

universe u v

namespace Langlands.NYLL.ValuationTheory.Valuations

/-- The native topology on a rank-one discrete valuation subring is adic for
its actual maximal ideal. -/
theorem rankOneDiscreteValuationSubring_isAdic :
    RankOneDiscreteValuationSubringIsAdicStatement.{u, v} := by
  intro K _ Gamma _ _ _
  let val := (Valued.v : _root_.Valuation K Gamma)
  let : IsTopologicalRing val.valuationSubring :=
    Subring.instIsTopologicalRing val.valuationSubring.toSubring
  rcases _root_.Valuation.exists_isUniformizer_of_isCyclic_of_nontrivial val with
    ⟨pi, hpi⟩
  have hmem (x : val.valuationSubring) (n : ℕ) :
      x ∈ IsLocalRing.maximalIdeal val.valuationSubring ^ n ↔
        val (x : K) ≤ val ((pi ^ n : val.valuationSubring) : K) := by
    rw [hpi.is_generator, Ideal.span_singleton_pow]
    simpa [Ideal.mem_span_singleton] using
      (_root_.Valuation.Integers.dvd_iff_le
        (_root_.Valuation.valuationSubring.integers (v := val))
        (x := pi ^ n) (y := x))
  rw [isAdic_iff]
  constructor
  · intro n
    have h_radius_ne :
        val (((pi ^ n : val.valuationSubring) : K)) ≠ 0 := by
      change val ((pi : K) ^ n) ≠ 0
      rw [map_pow]
      exact pow_ne_zero n hpi.val_ne_zero
    have h_restrict_radius_ne :
        val.restrict (((pi ^ n : val.valuationSubring) : K)) ≠ 0 := by
      simpa using h_radius_ne
    have h_open_ball_restrict : IsOpen
        {x : K |
          val.restrict x ≤
            val.restrict (((pi ^ n : val.valuationSubring) : K))} :=
      Valued.isOpen_closedBall K h_restrict_radius_ne
    have h_open_ball : IsOpen
        {x : K |
          val x ≤ val (((pi ^ n : val.valuationSubring) : K))} := by
      simpa only [val.restrict_le_iff] using h_open_ball_restrict
    have h_preimage_open : IsOpen
        {x : val.valuationSubring |
          val (x : K) ≤ val (((pi ^ n : val.valuationSubring) : K))} :=
      h_open_ball.preimage continuous_subtype_val
    convert h_preimage_open using 1
    ext x
    exact hmem x n
  · intro s hs
    rcases
        (mem_nhds_subtype (val.valuationSubring : Set K)
          (0 : val.valuationSubring) s).1 hs with
      ⟨t, ht, hts⟩
    rcases (Valued.hasBasis_nhds_zero K Gamma).mem_iff.mp ht with
      ⟨gamma, _hgamma, hgamma_t⟩
    let : MulArchimedean (MonoidWithZeroHom.ofClass val).ValueGroup₀ :=
      (_root_.Valuation.IsRankOneDiscrete.valueGroup₀_equiv_withZeroMulInt val).symm.mulArchimedean
    have hpi_restrict : val.restrict (pi : K) < 1 :=
      val.restrict_lt_one_iff.mpr hpi.val_lt_one
    obtain ⟨n, hn⟩ := exists_pow_lt₀ hpi_restrict gamma
    refine ⟨n, ?_⟩
    intro x hx
    apply hts
    apply hgamma_t
    change val.restrict (x : K) < gamma.1
    have hx_le := (hmem x n).mp hx
    calc
      val.restrict (x : K) ≤ val.restrict (((pi ^ n : val.valuationSubring) : K)) :=
        val.restrict_le_iff.mpr hx_le
      _ = val.restrict (pi : K) ^ n := map_pow val.restrict (pi : K) n
      _ < gamma.1 := hn

end Langlands.NYLL.ValuationTheory.Valuations
