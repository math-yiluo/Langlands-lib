import Langlands.HarmonicAnalysis.HarishChandraSchwartz.RationalXiSquareIntegrableOfUpperBound

/-! # Polynomial height summability on the actual uniformizer lattice -/

noncomputable section

universe u v

open CategoryTheory AlgebraicGeometry
open scoped CategoryTheory.MonObj NNReal ENNReal
open Langlands.GroupScheme Langlands.AlgebraicGeometry.PointTopology

namespace Langlands.HarishChandraSchwartz

attribute [local instance] rationalWeightsIsAffine rationalWeightsTopology
  rationalWeightsTopologicalGroup rationalWeightsT2Field rationalWeightsLocallyCompact

variable {F : Type u} [Field F] [ValuativeRel F] [TopologicalSpace F]
  [IsNonarchimedeanLocalField F]
  {S : CommGroupScheme (Spec (CommRingCat.of F))}
  {G : GroupScheme (Spec (CommRingCat.of F))} [IsAffineHom G.X.hom]
  (i : S.toGrp ⟶ G) (hS : IsSplitTorus S.toGrp) (hi : IsClosedSubgroup i)
  {n : Type} [Fintype n] [DecidableEq n] [Nonempty n]
  (ρ : MatrixRepresentation G n) (hρ : IsClosedSubgroup ρ)

/-- Polynomial decay in the actual uniformizer-point height is summable
in both the real and extended nonnegative real forms above one threshold. -/
def RationalUniformizerHeightSummability : Prop :=
  ∃ d : ℕ, ∀ r : ℝ, (d : ℝ) ≤ r →
    Summable (fun y : cocharacterLattice S =>
      (1 + rationalHeight (F := F) ρ (Aubert.General.uniformizerPowers i (.ofAdd y))) ^ (-r)) ∧
    (∑' y : cocharacterLattice S,
      ENNReal.ofReal ((1 + rationalHeight (F := F) ρ
        (Aubert.General.uniformizerPowers i (.ofAdd y))) ^ (-r))) < ⊤

include hS hi hρ

/-- Sufficiently large polynomial decay in the original matrix height is
summable on the whole actual cocharacter uniformizer lattice. -/
theorem exists_summable_rationalHeight_uniformizerPowers :
    ∃ d : ℕ, Summable (fun y : cocharacterLattice S =>
      (1 + rationalHeight (F := F) ρ (Aubert.General.uniformizerPowers i (.ofAdd y))) ^
        (-(d : ℝ))) := by
  obtain ⟨I, _, H, C, hH, hC, hb⟩ :=
    exists_cocharacterCoordinates_norm_le i hS hi ρ hρ
  let L := Submodule.span ℤ (Set.range (Pi.basisFun ℝ I))
  let d : ℕ := Module.finrank ℤ L + 1
  have hd : (Module.finrank ℤ L : ℝ) < (d : ℝ) := by dsimp [d]; norm_cast; omega
  have hd0 : 0 ≤ (d : ℝ) := Nat.cast_nonneg _
  have hz := (summable_one_add_norm_rpow_neg L hd).mul_left (C ^ (d : ℝ))
  have hsum := hz.comp_injective hH
  refine ⟨d, Summable.of_nonneg_of_le (fun y => Real.rpow_nonneg (by
    linarith [rationalHeight_nonneg ρ (Aubert.General.uniformizerPowers i (.ofAdd y))]) _) ?_ hsum⟩
  intro y
  have hs : 0 < 1 + rationalHeight (F := F) ρ
      (Aubert.General.uniformizerPowers i (.ofAdd y)) := by
    linarith [rationalHeight_nonneg ρ (Aubert.General.uniformizerPowers i (.ofAdd y))]
  have hn : 0 < 1 + ‖H y‖ := by positivity
  have hle : (1 + ‖H y‖) / C ≤
      1 + rationalHeight (F := F) ρ (Aubert.General.uniformizerPowers i (.ofAdd y)) := by
    rw [div_le_iff₀ hC]
    simpa only [mul_comm] using hb y
  calc
    (1 + rationalHeight (F := F) ρ (Aubert.General.uniformizerPowers i (.ofAdd y))) ^
        (-(d : ℝ)) ≤ ((1 + ‖H y‖) / C) ^ (-(d : ℝ)) :=
      Real.rpow_le_rpow_of_nonpos (div_pos hn hC) hle (neg_nonpos.mpr hd0)
    _ = C ^ (d : ℝ) * (1 + ‖H y‖) ^ (-(d : ℝ)) := by
      rw [Real.div_rpow hn.le hC.le, Real.rpow_neg hC.le, div_inv_eq_mul, mul_comm]

/-- Every exponent beyond one finite threshold is summable, in both the real
and the ENNReal form used by the quotient-cell integral estimates. -/
theorem exists_rationalHeight_uniformizerPowers_tsum_lt_top :
    RationalUniformizerHeightSummability i ρ := by
  obtain ⟨d, hd⟩ := exists_summable_rationalHeight_uniformizerPowers i hS hi ρ hρ
  refine ⟨d, fun r hr => ?_⟩
  have hsum : Summable (fun y : cocharacterLattice S =>
      (1 + rationalHeight (F := F) ρ (Aubert.General.uniformizerPowers i (.ofAdd y))) ^ (-r)) := by
    apply Summable.of_nonneg_of_le (fun y => Real.rpow_nonneg (by
      linarith [rationalHeight_nonneg ρ (Aubert.General.uniformizerPowers i (.ofAdd y))]) _)
      (fun y => ?_) hd
    exact Real.rpow_le_rpow_of_exponent_le
      (by linarith [rationalHeight_nonneg ρ (Aubert.General.uniformizerPowers i (.ofAdd y))])
      (neg_le_neg hr)
  exact ⟨hsum, hsum.tsum_ofReal_lt_top⟩

/-- Restriction along any injective parametrization preserves the same
threshold, including chamber sublattices and corrected positive orthants. -/
theorem exists_rationalHeight_uniformizerPowers_comp_tsum_lt_top
    {J : Type v} (e : J → cocharacterLattice S) (he : Function.Injective e) :
    ∃ d : ℕ, ∀ r : ℝ, (d : ℝ) ≤ r →
      Summable (fun j : J =>
        (1 + rationalHeight (F := F) ρ (Aubert.General.uniformizerPowers i (.ofAdd (e j)))) ^
          (-r)) ∧
      (∑' j : J, ENNReal.ofReal ((1 + rationalHeight (F := F) ρ
        (Aubert.General.uniformizerPowers i (.ofAdd (e j)))) ^ (-r))) < ⊤ := by
  obtain ⟨d, hd⟩ := exists_rationalHeight_uniformizerPowers_tsum_lt_top i hS hi ρ hρ
  refine ⟨d, fun r hr => ?_⟩
  have hsum := ((hd r hr).1).comp_injective he
  exact ⟨hsum, hsum.tsum_ofReal_lt_top⟩

end Langlands.HarishChandraSchwartz
