import Langlands.Representation.Archimedean.RealInducedSwapRecurrent
import Langlands.Representation.Archimedean.RealAmbientOrthogonalUncertainty

/-!
# Finite-support cancellation of recurrent induction-block crossings

Parity strengthens the induction window by one. Adjacent uncertainty then
annihilates finite middle or final crossing composites, including the endpoint.
-/

noncomputable section

open scoped TensorProduct Matrix Manifold ContDiff Matrix.Norms.Operator

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

namespace Langlands.Archimedean
namespace RealInducedSwapCancellation

open Langlands.GeneralLinear Langlands.LocalFactor.Archimedean
open RealBlockFrobeniusMap RealBlockPosition RealBlockMultiplier RealCharacterPair
open RealCharacterPairReducible RealBlockJacquet RealStandardFiltration
open RealCharacterInducedSwap RealCharacterInducedPushforward
open RealInducedSwapGeneric RealInducedSwapRecurrent

/-- The multiplier vanishes at every mode whose absolute index is at least `L`. -/
def FiniteModes (L : ℕ) (μ : ℤ → ℂ) : Prop :=
  ∀ j : ℤ, (L : ℤ) ≤ |j| → μ j = 0

/-- In any ambient rank, an induction block has no modes below `|weight|+1`. -/
theorem induced_low_modes {n : ℕ} {ds : List RealBlock}
    (hr : realRank ds = n) {p : ℕ} {d : ComplexCharacterData}
    (hd : realInducedBlockAt ds p = some d) (f : KF n ds) (j : ℤ)
    (hj : |j| < ((d.weight.natAbs + 1 : ℕ) : ℤ)) (g : Langlands.GeneralLinear n ℝ) :
    blockFourierCoefficient n p j (f : Langlands.GeneralLinear n ℝ → ℂ) g = 0 := by
  by_cases hlow : |j| < (d.weight.natAbs : ℤ)
  · exact f.2.1.2 p d hd j (by simpa only [Int.abs_eq_natAbs] using hlow) g
  · obtain ⟨hc1, hc2, _, _⟩ := RealKTypeTransport.realInducedBlockAt_eq_some hd
    have hpar : (-1 : ℂ) ^ ((d.weight.natAbs + 1 : ℕ) : ℤ) =
        realPositionCharacter ds p (-1) * realPositionCharacter ds (p + 1) (-1) := by
      have a1 : realInducedFirstCharacter d (-1) = (-1) ^ (d.weight.natAbs + 1) := by
        simp [realInducedFirstCharacter]
      have a2 : realInducedSecondCharacter d (-1) = 1 := by
        simp [realInducedSecondCharacter]
      rw [hc1, hc2, zpow_natCast, a1, a2, mul_one]
    refine blockFourierCoefficient_eq_zero_of_not_even
      (hr ▸ realInducedBlockAt_lt hd) hpar f ?_ g
    rw [Int.even_iff]
    have he : |j| = (d.weight.natAbs : ℤ) := by omega
    by_cases hjnonneg : 0 ≤ j
    · rw [abs_of_nonneg hjnonneg] at he
      omega
    · rw [abs_of_neg (by omega)] at he
      omega

/-- A standard-module vector with finite modes adjacent to an induction window is zero.
The cutoff may equal the induction weight, since the boundary mode has wrong parity. -/
theorem eq_zero_of_induced_finite {n : ℕ} {ds : List RealBlock}
    (hr : realRank ds = n) (p : ℕ) (hp : p + 3 ≤ n) {r s L : ℕ}
    (hrs : r = 0 ∧ s = 1 ∨ r = 1 ∧ s = 0) {d : ComplexCharacterData}
    (hd : realInducedBlockAt ds (p + r) = some d) (hL : L ≤ d.weight.natAbs)
    (f : KF n ds)
    (hlow : ∀ g ∈ unitaryCompact ℝ n, ∀ j : ℤ, (L : ℤ) ≤ |j| →
      blockFourierCoefficient n (p + s) j (f : Langlands.GeneralLinear n ℝ → ℂ) g = 0) :
    f = 0 := by
  apply Subtype.ext
  apply eq_zero_of_mem_principalSeries_of_eqOn_unitaryCompact f.2.1.1
  exact RealOrthogonalBlock.adjacent_uncertainty p hp hrs (Nat.lt_succ_of_le hL)
    (contMDiff_of_mem_realStandardModule f.2.1).continuous f.2.2
    (fun g _ j hj => induced_low_modes hr hd f j hj g) hlow

variable (d e : ComplexCharacterData) (h : FourCrossings d e)

/-- A finite `AC` factor annihilates the first two crossings if its cutoff is at most
that of the transported first induction block. -/
theorem first_two_eq_zero {L : ℕ} (hL : L ≤ d.weight.natAbs)
    (hfinite : FiniteModes L h.ac.μ)
    (f : KF 4 (source d e)) :
    blockFrobMap (RealInducedSwapRecurrent.dataAC d e h)
      (blockFrobMap (RealInducedSwapRecurrent.dataBC d e h)
        (Submodule.inclusion (source_le_expanded d e) f)) = 0 := by
  let f0 : KF 4 (expanded d e) := Submodule.inclusion (source_le_expanded d e) f
  let H : KF 4 (crossed d e) := blockFrobMap (RealInducedSwapRecurrent.dataBC d e h) f0
  let U : KF 4 (movedLeft d e) := blockFrobMap (RealInducedSwapRecurrent.dataAC d e h) H
  let U' : KF 4 (firstMoved d e) :=
    ⟨(U : Langlands.GeneralLinear 4 ℝ → ℂ),
      mem_firstMoved d e U (RealInducedSwapRecurrent.first_window_once d e h f)⟩
  have hz : U' = 0 := by
    apply eq_zero_of_induced_finite (n := 4) (ds := firstMoved d e) rfl 0 (by decide)
      (r := 1) (s := 0) (Or.inr ⟨rfl, rfl⟩) (d := d) rfl hL U'
    intro g hg j hj
    change blockFourierCoefficient 4 0 j (U : Langlands.GeneralLinear 4 ℝ → ℂ) g = 0
    rw [blockFourierCoefficient_blockFrobMap (RealInducedSwapRecurrent.dataAC d e h) H hg j,
      hfinite j hj, zero_mul]
  apply Subtype.ext
  exact congrArg (fun x : KF 4 (firstMoved d e) =>
    (x : Langlands.GeneralLinear 4 ℝ → ℂ)) hz

/-- The disjoint alternative first two crossings vanish for a finite `BD` factor
below or at the transported second induction weight. -/
theorem second_two_eq_zero {L : ℕ} (hL : L ≤ e.weight.natAbs)
    (hfinite : FiniteModes L h.bd.μ)
    (f : KF 4 (source d e)) :
    blockFrobMap (RealInducedSwapRecurrent.dataBD' d e h)
      (blockFrobMap (RealInducedSwapRecurrent.dataBC d e h)
        (Submodule.inclusion (source_le_expanded d e) f)) = 0 := by
  let f0 : KF 4 (expanded d e) := Submodule.inclusion (source_le_expanded d e) f
  let H : KF 4 (crossed d e) := blockFrobMap (RealInducedSwapRecurrent.dataBC d e h) f0
  let U : KF 4 (movedRight d e) := blockFrobMap (RealInducedSwapRecurrent.dataBD' d e h) H
  let U' : KF 4 (secondMoved d e) :=
    ⟨(U : Langlands.GeneralLinear 4 ℝ → ℂ),
      mem_secondMoved d e U (RealInducedSwapRecurrent.second_window_once d e h f)⟩
  have hz : U' = 0 := by
    apply eq_zero_of_induced_finite (n := 4) (ds := secondMoved d e) rfl 1 (by decide)
      (r := 0) (s := 1) (Or.inl ⟨rfl, rfl⟩) (d := e) rfl hL U'
    intro g hg j hj
    change blockFourierCoefficient 4 2 j (U : Langlands.GeneralLinear 4 ℝ → ℂ) g = 0
    rw [blockFourierCoefficient_blockFrobMap (RealInducedSwapRecurrent.dataBD' d e h) H hg j,
      hfinite j hj, zero_mul]
  apply Subtype.ext
  exact congrArg (fun x : KF 4 (secondMoved d e) =>
    (x : Langlands.GeneralLinear 4 ℝ → ℂ)) hz

/-- A finite `AC` crossing below the first induction weight annihilates the whole map. -/
theorem rawMap_eq_zero_of_finite_ac {L : ℕ} (hL : L ≤ d.weight.natAbs)
    (hfinite : FiniteModes L h.ac.μ) :
    RealInducedSwapRecurrent.rawMap d e h = 0 := by
  ext f : 1
  change blockFrobMap (RealInducedSwapRecurrent.dataAD d e h)
    (blockFrobMap (RealInducedSwapRecurrent.dataBD d e h)
      (blockFrobMap (RealInducedSwapRecurrent.dataAC d e h)
        (blockFrobMap (RealInducedSwapRecurrent.dataBC d e h)
          (Submodule.inclusion (source_le_expanded d e) f)))) = 0
  rw [first_two_eq_zero d e h hL hfinite f, map_zero, map_zero]

/-- A finite `BD` crossing below the second induction weight annihilates the whole map. -/
theorem rawMap_eq_zero_of_finite_bd {L : ℕ} (hL : L ≤ e.weight.natAbs)
    (hfinite : FiniteModes L h.bd.μ) :
    RealInducedSwapRecurrent.rawMap d e h = 0 := by
  ext f : 1
  change blockFrobMap (RealInducedSwapRecurrent.dataAD d e h)
    (blockFrobMap (RealInducedSwapRecurrent.dataBD d e h)
      (blockFrobMap (RealInducedSwapRecurrent.dataAC d e h)
        (blockFrobMap (RealInducedSwapRecurrent.dataBC d e h)
          (Submodule.inclusion (source_le_expanded d e) f)))) = 0
  rw [RealInducedSwapRecurrent.middle_square,
    second_two_eq_zero d e h hL hfinite f, map_zero, map_zero]

/-- A finite final `AD` factor with cutoff at most the first target induction weight
annihilates the recurrent map. -/
theorem recurrentMap_eq_zero_of_finite_ad_first {L : ℕ} (hL : L ≤ d.weight.natAbs)
    (hfinite : FiniteModes L h.ad.μ) :
    recurrentMap d e h = 0 := by
  ext f : 1
  change recurrentMap d e h f = 0
  apply eq_zero_of_induced_finite (n := 4) (ds := target d e) rfl 1 (by decide)
    (r := 1) (s := 0) (Or.inr ⟨rfl, rfl⟩) (d := d) rfl hL (recurrentMap d e h f)
  intro g hg j hj
  change blockFourierCoefficient 4 1 j
    (RealInducedSwapRecurrent.rawMap d e h f : Langlands.GeneralLinear 4 ℝ → ℂ) g = 0
  rw [RealInducedSwapRecurrent.rawMap, LinearMap.comp_apply, LinearMap.comp_apply,
    LinearMap.comp_apply, LinearMap.comp_apply,
    blockFourierCoefficient_blockFrobMap (RealInducedSwapRecurrent.dataAD d e h) _ hg j,
    hfinite j hj, zero_mul]

/-- The same final-factor cancellation against the second target induction window. -/
theorem recurrentMap_eq_zero_of_finite_ad_second {L : ℕ} (hL : L ≤ e.weight.natAbs)
    (hfinite : FiniteModes L h.ad.μ) :
    recurrentMap d e h = 0 := by
  ext f : 1
  change recurrentMap d e h f = 0
  apply eq_zero_of_induced_finite (n := 4) (ds := target d e) rfl 0 (by decide)
    (r := 0) (s := 1) (Or.inl ⟨rfl, rfl⟩) (d := e) rfl hL (recurrentMap d e h f)
  intro g hg j hj
  change blockFourierCoefficient 4 1 j
    (RealInducedSwapRecurrent.rawMap d e h f : Langlands.GeneralLinear 4 ℝ → ℂ) g = 0
  rw [RealInducedSwapRecurrent.rawMap, LinearMap.comp_apply, LinearMap.comp_apply,
    LinearMap.comp_apply, LinearMap.comp_apply,
    blockFourierCoefficient_blockFrobMap (RealInducedSwapRecurrent.dataAD d e h) _ hg j,
    hfinite j hj, zero_mul]

end RealInducedSwapCancellation
end Langlands.Archimedean
