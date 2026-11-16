import Langlands.Representation.Archimedean.RealBlockFourierPropagation
import Langlands.Representation.Archimedean.RealBlockFourierFinite
import Langlands.Representation.Archimedean.RealStrictCharacterLanglandsQuotient

/-!
# Fourier conditions on `O(N)` suffice for real standard modules

A function `f` of the principal series of the position characters of a list of real blocks
`ds` with `realRank ds = N` lies in the real standard module `realStandardModule N ds` as soon
as its block Fourier coefficients `Φ_k f (κ)` of weight `|k| < |m|` vanish at every `κ ∈ O(N)`,
for every induction block of weight `m`. Modes `k` with `k + |m| + 1` even are propagated from
`O(N)` to `GL_N(ℝ)` by `RealBlockPropagation.blockFourierCoefficient_window_eq_zero`; the other
modes vanish everywhere by parity.
-/

noncomputable section

open scoped Manifold ContDiff Matrix.Norms.Operator

set_option autoImplicit false

namespace Langlands.Archimedean

namespace InductionStages

open Langlands.GeneralLinear Langlands.LocalFactor.Archimedean GramFormula

set_option backward.isDefEq.respectTransparency false

/-- `χ_l(e^x) = e^{τ_l x}` for the position characters and exponents of a list of blocks. -/
theorem realPositionCharacter_exp (ds : List RealBlock) (l : ℕ) (x : ℝ) :
    realPositionCharacter ds l (Units.mk0 (Real.exp x) (Real.exp_pos x).ne') =
      Complex.exp (realPositionExponent ds l * x) := by
  rw [realPositionCharacter_eq_signUnit_mul]
  have hs : signUnit (Units.mk0 (Real.exp x) (Real.exp_pos x).ne') = 1 := by
    simp [signUnit, Real.exp_pos]
  rw [hs, RealStrictCharacterLanglandsQuotient.realPositionCharacter_one, one_mul, Units.val_mk0,
    abs_of_pos (Real.exp_pos x), RealPrincipalSeriesDuality.ofReal_exp_cpow, mul_comm]

/-- The characters and exponents at the two positions of an induction block. -/
theorem realPosition_of_realInducedBlockAt : ∀ {ds : List RealBlock} {p : ℕ}
    {d : ComplexCharacterData}, realInducedBlockAt ds p = some d →
      realPositionCharacter ds p = realInducedFirstCharacter d ∧
        realPositionCharacter ds (p + 1) = realInducedSecondCharacter d ∧
        realPositionExponent ds p = d.exponent + (d.weight.natAbs : ℂ) / 2 ∧
        realPositionExponent ds (p + 1) = d.exponent - (d.weight.natAbs : ℂ) / 2
  | [], _, _, h => by simp [realInducedBlockAt] at h
  | .character _ :: _, 0, _, h => by simp [realInducedBlockAt] at h
  | .character _ :: ds, p + 1, _, h => realPosition_of_realInducedBlockAt (ds := ds) (p := p) h
  | .induced _ :: _, 0, _, h => by
      simp only [realInducedBlockAt, Option.some.injEq] at h
      subst h
      exact ⟨rfl, rfl, rfl, rfl⟩
  | .induced _ :: _, 1, _, h => by simp [realInducedBlockAt] at h
  | .induced _ :: ds, p + 2, _, h => realPosition_of_realInducedBlockAt (ds := ds) (p := p) h

theorem realInducedFirstCharacter_neg_one (d : ComplexCharacterData) :
    realInducedFirstCharacter d (-1) = (-1 : ℂ) ^ (d.weight.natAbs + 1) := by
  simp [realInducedFirstCharacter]

theorem realInducedSecondCharacter_neg_one (d : ComplexCharacterData) :
    realInducedSecondCharacter d (-1) = 1 := by
  simp [realInducedSecondCharacter]

/-- **Fourier conditions on `O(N)`.** If `f` lies in the principal series of the position
characters of `ds`, `realRank ds = N`, and the block Fourier coefficients of weight `|k| < |m|`
of every induction block of weight `m` vanish on `O(N)`, then `f ∈ realStandardModule N ds`. -/
theorem mem_realStandardModule_of_unitaryCompact {N : ℕ} {ds : List RealBlock}
    (hN : realRank ds = N) {f : Langlands.GeneralLinear N ℝ → ℂ}
    (hf : f ∈ principalSeries ℝ N (realPositionCharacter ds))
    (hK : ∀ (p : ℕ) (d : ComplexCharacterData), realInducedBlockAt ds p = some d →
      ∀ k : ℤ, |k| < |d.weight| → ∀ κ ∈ unitaryCompact ℝ N,
        blockFourierCoefficient N p k f κ = 0) :
    f ∈ realStandardModule N ds := by
  refine ⟨hf, fun p d hd k hk g => ?_⟩
  have hp : p + 1 < N := hN ▸ realInducedBlockAt_lt hd
  obtain ⟨hc1, hc2, he1, he2⟩ := realPosition_of_realInducedBlockAt hd
  have hkM : |k| < (d.weight.natAbs : ℤ) := by rwa [Int.abs_eq_natAbs d.weight] at hk
  by_cases hev : Even (k + (d.weight.natAbs : ℤ) + 1)
  · -- the window: propagation from `O(N)`
    have hα := RealBlockDerivative.isExpEquivariant_of_mem_principalSeries
      (τ := fun i : Fin N => realPositionExponent ds i)
      (fun i x => realPositionCharacter_exp ds i x) hf
    have hδ : (realPositionExponent ds ((RealBlockRotation.ia hp : Fin N) : ℕ) +
        ((N : ℂ) - 1) / 2 - (((RealBlockRotation.ia hp : Fin N) : ℕ) : ℂ)) -
        (realPositionExponent ds ((RealBlockRotation.ib hp : Fin N) : ℕ) +
        ((N : ℂ) - 1) / 2 - (((RealBlockRotation.ib hp : Fin N) : ℕ) : ℂ)) =
        (d.weight.natAbs : ℂ) + 1 := by
      simp only [RealBlockRotation.ia, RealBlockRotation.ib, he1, he2]
      push_cast
      ring
    exact RealBlockPropagation.blockFourierCoefficient_window_eq_zero hp hf.1 hα hδ
      (fun κ hκ j hj => hK p d hd j (by
        rw [Int.abs_eq_natAbs d.weight]
        exact (RealBlockPropagation.mem_window.mp hj).1) κ hκ) g k
      (RealBlockPropagation.mem_window.mpr ⟨hkM, hev⟩)
  · -- the other modes: parity
    refine RealBlockFourierFinite.blockFourierCoefficient_eq_zero_of_parity hp
      (RealStrictCharacterLanglandsQuotient.realPositionCharacter_one ds) hf ?_ g
    rw [hc1, hc2, realInducedFirstCharacter_neg_one, realInducedSecondCharacter_neg_one, mul_one]
    intro h
    have hodd : Odd (k + (d.weight.natAbs : ℤ) + 1) := Int.not_even_iff_odd.mp hev
    have h1 : (-1 : ℂ) ^ (k + (d.weight.natAbs : ℤ) + 1) = -1 := hodd.neg_one_zpow
    have h2 : (-1 : ℂ) ^ (k + (d.weight.natAbs : ℤ) + 1) =
        (-1 : ℂ) ^ k * (-1 : ℂ) ^ (((d.weight.natAbs + 1 : ℕ) : ℤ)) := by
      rw [← zpow_add₀ (by norm_num : (-1 : ℂ) ≠ 0)]
      congr 1
      push_cast
      ring
    rw [h2, h, zpow_natCast, ← mul_pow, neg_one_mul, neg_neg, one_pow] at h1
    norm_num at h1

end InductionStages

end Langlands.Archimedean
