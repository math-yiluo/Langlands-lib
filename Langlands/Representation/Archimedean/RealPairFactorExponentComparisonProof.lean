import Langlands.Representation.Archimedean.ComplexJacquetBorel
import Langlands.Representation.Archimedean.RealJacquetFrobeniusProof
import Langlands.Representation.Archimedean.RealPairFactorExponentComparisonStatement
import Langlands.Representation.Archimedean.RealPairLFactorRegularityProof

set_option autoImplicit false

namespace Langlands.Archimedean

open Langlands.LocalFactor.Archimedean

private theorem exists_test_with_pole {xs : List RealBlock} {x : RealBlock} (hx : x ∈ xs) :
    ∃ (z : RealBlock) (s : ℂ), realBlockExponent z = 0 ∧
      s.re = -realBlockExponent x ∧ (realPairLFactor xs [z]).denominator s = 0 := by
  cases x with
  | character c =>
    let d := RealJacquetFrobenius.charData c.parity 0
    refine ⟨.character d, -c.exponent, rfl, Complex.neg_re _, ?_⟩
    have hmem : .character (c.mul d) ∈ realPairBlocks xs [.character d] :=
      mem_realPairBlocks.mpr ⟨.character c, hx, .character d, by simp, by simp [RealBlock.tensor]⟩
    have hpar : (c.mul d).parity = 0 := by
      change c.parity + c.parity = 0
      apply Fin.ext
      have hc := c.parity.isLt
      simp only [Fin.val_add, Fin.val_zero]
      omega
    change (realLFactor (realPairBlocks xs [.character d])).IsPole (-c.exponent)
    apply (realLFactor_isPole _ _).mpr
    have hd : d.exponent = 0 := rfl
    exact .inl ⟨c.mul d, hmem, 0, by simp [hpar, hd]⟩
  | induced c =>
    let d := characterOfParams c.weight 0
    refine ⟨.induced d, -c.exponent, rfl, Complex.neg_re _, ?_⟩
    have hmem : .induced (c.mul d.conj) ∈ realPairBlocks xs [.induced d] :=
      mem_realPairBlocks.mpr ⟨.induced c, hx, .induced d, by simp, by simp [RealBlock.tensor]⟩
    have hw : (c.mul d.conj).weight = 0 := by
      change c.weight + -c.weight = 0
      exact add_neg_cancel _
    change (realLFactor (realPairBlocks xs [.induced d])).IsPole (-c.exponent)
    apply (realLFactor_isPole _ _).mpr
    exact .inr ⟨c.mul d.conj, hmem, 0, by simp [hw, d]⟩

/-- A pole detected by a singleton test at the negative of a block exponent must also
occur for the comparison list. Right half-plane regularity then gives the lower bound. -/
theorem realPairFactorExponentComparison : RealPairFactorExponentComparisonStatement := by
  intro xs ys a hLower hEq x hx
  obtain ⟨z, s, hz, hs, hpole⟩ := exists_test_with_pole hx
  by_contra! hxa
  have hreg : (realPairLFactor ys [z]).denominator s ≠ 0 := by
    apply realPairLFactorRightHalfPlaneRegularity
    intro y hy w hw
    have h := hLower y hy
    obtain rfl : w = z := List.mem_singleton.mp hw
    linarith
  rw [hEq z hz] at hpole
  exact hreg hpole

end Langlands.Archimedean
