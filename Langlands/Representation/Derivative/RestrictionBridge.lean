import Langlands.Representation.Derivative.LevelCalculus

/-!
# General linear derivatives through the mirabolic restriction

The published `GL` derivative of positive order is the mirabolic derivative of
the restriction, up to the actual rank transports. This module records that
identification at the level of objects and of nonvanishing, and the
homogeneity of a mirabolic representation whose nonzero derivatives all have
one order.
-/

noncomputable section

open CategoryTheory

namespace Langlands.Derivative

open GeneralLinear HarmonicAnalysis

universe uF uV

variable {p : ℕ} [Fact p.Prime] {F : PadicField.{uF} p}

namespace RestrictionBridge

open LevelCalculus

variable (T : F.TopologicalData) (ψ : @UnitaryAdditiveCharacter F.Carrier _ T.topology)

/-- Restriction after a rank transport is the transported restriction. -/
theorem generalLinearRestriction_rankCast_obj {n c : ℕ} (e : n + 1 = c + 1) (e' : n = c) :
    letI := T.topology
    ∀ A : SmoothRep.{0, uF, uV} ℂ (GeneralLinear (n + 1) F.Carrier),
      (generalLinearRestriction T c).obj ((generalLinearRankCast T e).obj A) =
        (mirabolicRankCast T e').obj ((generalLinearRestriction T n).obj A) := by
  subst e'
  intro A
  rfl

/-- The positive-order `GL` derivative is the mirabolic derivative of the
restriction, with no further transport. -/
theorem generalLinearDerivative_succ_obj_eq {n j : ℕ} (hk : j + 1 ≤ n + 1)
    (hk' : 0 < j + 1 ∧ j + 1 ≤ n + 1) :
    letI := T.topology
    ∀ A : SmoothRep.{0, uF, uV} ℂ (GeneralLinear (n + 1) F.Carrier),
      (generalLinearDerivative T ψ (n + 1) (j + 1) hk).obj A =
        (mirabolicDerivativeOfOrder T ψ n (j + 1) hk').obj
          ((generalLinearRestriction T n).obj A) := by
  intro A
  rw [generalLinearDerivative_succ_obj, generalLinearDerivativePositive_obj,
    mirabolicDerivativeOfOrder_obj,
    generalLinearRestriction_rankCast_obj T (rank_eq_of_succ_le hk) (by omega)]
  rfl

/-- The same identification, for a source given on an equal rank. -/
theorem generalLinearDerivative_obj_eq_cast {a n k : ℕ} (ha : a = n + 1) (hk : k ≤ a)
    (hk' : 0 < k ∧ k ≤ n + 1) (h : a - k = n + 1 - k) :
    letI := T.topology
    ∀ A : SmoothRep.{0, uF, uV} ℂ (GeneralLinear a F.Carrier),
      (generalLinearRankCast T h).obj ((generalLinearDerivative T ψ a k hk).obj A) =
        (mirabolicDerivativeOfOrder T ψ n k hk').obj
          ((generalLinearRestriction T n).obj ((generalLinearRankCast T ha).obj A)) := by
  subst ha
  obtain _ | j := k
  · exact absurd hk'.1 (Nat.lt_irrefl 0)
  · intro A
    exact generalLinearDerivative_succ_obj_eq T ψ hk hk' A

theorem nontrivial_generalLinearRankCast_iff {a b : ℕ} (h : a = b) :
    letI := T.topology
    ∀ A : SmoothRep.{0, uF, uV} ℂ (GeneralLinear a F.Carrier),
      Nontrivial ((generalLinearRankCast T h).obj A) ↔ Nontrivial A := by
  subst h
  intro A
  rfl

theorem nontrivial_generalLinearDerivative_iff {a n k : ℕ} (ha : a = n + 1) (hk : k ≤ a)
    (hpos : 0 < k) :
    letI := T.topology
    ∀ A : SmoothRep.{0, uF, uV} ℂ (GeneralLinear a F.Carrier),
      Nontrivial ((generalLinearDerivative T ψ a k hk).obj A) ↔
        HasNonzeroDerivative T ψ
          ((generalLinearRestriction T n).obj ((generalLinearRankCast T ha).obj A)) k := by
  intro A
  have hk' : 0 < k ∧ k ≤ n + 1 := ⟨hpos, by omega⟩
  rw [hasNonzeroDerivative_iff T ψ hk', ← generalLinearDerivative_obj_eq_cast T ψ ha hk hk'
    (by omega) A]
  exact (nontrivial_generalLinearRankCast_iff T _ _).symm

section Single

variable (hE : Mirabolic.MinusExactnessStatement.{uF, uV} F T)
include hE

/-- A mirabolic representation whose nonzero derivatives all have one order
`c` is homogeneous: every nonzero subrepresentation has a nonzero derivative
(detection), of an order that is nonzero for the whole representation
(exactness). -/
theorem isHomogeneous_of_single_order {N : ℕ} (c : ℕ) :
    letI := T.topology
    ∀ A : SmoothRep.{0, uF, uV} ℂ (mirabolic N F.Carrier),
      (∀ j, HasNonzeroDerivative T ψ A j → j = c) → IsHomogeneous T ψ A := by
  intro A hA
  apply isHomogeneous_of_forall_injective T ψ A c
  intro W f hf hW
  exact hA _ (hasNonzeroDerivative_of_injective T ψ hE f hf _
    (hasNonzeroDerivative_level T ψ W (level_pos T ψ W).ne'))

end Single

end RestrictionBridge

end Langlands.Derivative
