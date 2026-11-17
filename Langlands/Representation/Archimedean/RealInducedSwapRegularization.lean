import Langlands.Representation.Archimedean.RealInducedSwapRegularizedFamily

/-!
# Cancellation and division for the actual four-crossing family

Finite-support cancellation removes the residue on the two induction windows.
Away from zero the regularized family is an explicit scalar multiple of the
generic shifted family.
-/

noncomputable section

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

namespace Langlands.Archimedean
namespace RealInducedSwapRegularization

open Langlands.LocalFactor.Archimedean
open RealBlockMultiplier RealBlockFrobeniusMap RealCharacterPair
open RealCharacterPairReducible RealInducedSwapGeneric
open RealBlockMultiplierAnalytic RealFiniteLayerRegularization RealKTypeCount
open RealCharacterInducedSwap RealCharacterInducedPushforward
open RealInducedSwapRegularizedFamily RealInducedSwapCancellation
open RealBlockJacquet

/-- A scalar relation on the actual source parity class scales the Frobenius map. -/
theorem blockFrobMap_eq_smul_of_eq_on_parity
    {n p : ℕ} {ds es : List RealBlock} {ε : ℤ} {σ τ a : ℂ} {μ ν : ℤ → ℂ}
    (h : IsBlockFrobData n ds es p ε σ μ) (h' : IsBlockFrobData n ds es p ε τ ν)
    (hμν : ∀ j : ℤ, Even (j - ε) → μ j = a * ν j) :
    blockFrobMap h = a • blockFrobMap h' := by
  ext f : 1
  refine eq_of_blockFourierCoefficient_eq h.lt fun j k hk => ?_
  change blockFourierCoefficient n p j (blockFrobMap h f) k =
    blockFourierCoefficient n p j (a • blockFrobMap h' f) k
  rw [blockFourierCoefficient_blockFrobMap h _ hk,
    blockFourierCoefficient_smul, blockFourierCoefficient_blockFrobMap h' _ hk]
  by_cases hj : Even (j - ε)
  · rw [hμν j hj, mul_assoc]
  · rw [blockFourierCoefficient_eq_zero_of_not_even h.lt h.par f hj k,
      mul_zero, mul_zero, mul_zero]

variable (d e : ComplexCharacterData) (c : Choices)

/-- The number of removed denominators in the four crossings. -/
def totalOrder : ℕ := order c.ad + order c.bd + order c.ac + order c.bc

/-- A finite middle or final multiplier has a cutoff bounded by an adjacent
induction weight. These are explicit sufficient residue-cancellation conditions. -/
def Cancels : Prop :=
  (∃ L : ℕ, L ≤ d.weight.natAbs ∧
    FiniteModes L (multiplier ((chA d).exponent - (chA e).exponent)
      (pairParity (chA e) (chA d)) c.ac 0)) ∨
  (∃ L : ℕ, L ≤ e.weight.natAbs ∧
    FiniteModes L (multiplier ((chB d).exponent - (chB e).exponent)
      (pairParity (chB e) (chB d)) c.bd 0)) ∨
  (∃ L : ℕ, L ≤ max d.weight.natAbs e.weight.natAbs ∧
    FiniteModes L (multiplier ((chA d).exponent - (chB e).exponent)
      (pairParity (chB e) (chA d)) c.ad 0))

theorem rawMap_zero_of_finite_ac (hc : Valid d e c) {L : ℕ}
    (hL : L ≤ d.weight.natAbs)
    (hf : FiniteModes L (multiplier ((chA d).exponent - (chA e).exponent)
      (pairParity (chA e) (chA d)) c.ac 0)) :
    rawMap d e c 0 = 0 := by
  rw [rawMap_zero_eq_recurrent d e c hc]
  exact rawMap_eq_zero_of_finite_ac d e (atZero d e c hc) hL hf

theorem rawMap_zero_of_finite_bd (hc : Valid d e c) {L : ℕ}
    (hL : L ≤ e.weight.natAbs)
    (hf : FiniteModes L (multiplier ((chB d).exponent - (chB e).exponent)
      (pairParity (chB e) (chB d)) c.bd 0)) :
    rawMap d e c 0 = 0 := by
  rw [rawMap_zero_eq_recurrent d e c hc]
  exact rawMap_eq_zero_of_finite_bd d e (atZero d e c hc) hL hf

theorem rawMap_zero_of_finite_ad (hc : Valid d e c) {L : ℕ}
    (hL : L ≤ max d.weight.natAbs e.weight.natAbs)
    (hf : FiniteModes L (multiplier ((chA d).exponent - (chB e).exponent)
      (pairParity (chB e) (chA d)) c.ad 0)) :
    rawMap d e c 0 = 0 := by
  have hz : RealInducedSwapRecurrent.recurrentMap d e (atZero d e c hc) = 0 := by
    rcases le_max_iff.mp hL with hL | hL
    · exact recurrentMap_eq_zero_of_finite_ad_first d e (atZero d e c hc) hL hf
    · exact recurrentMap_eq_zero_of_finite_ad_second d e (atZero d e c hc) hL hf
  rw [rawMap_zero_eq_recurrent d e c hc]
  ext f : 1
  apply Subtype.ext
  exact congrArg
    (fun v : KF 4 (target d e) => (v : Langlands.GeneralLinear 4 ℝ → ℂ))
    (LinearMap.congr_fun hz f)

/-- Cancellation holds on the actual induction subspace. -/
theorem rawMap_zero (hc : Valid d e c) (hcan : Cancels d e c) :
    rawMap d e c 0 = 0 := by
  rcases hcan with ⟨L, hL, hf⟩ | ⟨L, hL, hf⟩ | ⟨L, hL, hf⟩
  · exact rawMap_zero_of_finite_ac d e c hc hL hf
  · exact rawMap_zero_of_finite_bd d e c hc hL hf
  · exact rawMap_zero_of_finite_ad d e c hc hL hf

/-- The actual ambient composite has precisely the scalar factors introduced
by the erased denominators. -/
theorem fullMap_eq_scaled_generic (hc : Valid d e c) {z : ℂ} (hz : z ≠ 0)
    (hg : RealInducedSwapInverse.IsGenericShift d e z) :
    fullMap d e c z = z ^ totalOrder c •
      RealInducedSwapInverse.fullMap (RealInducedSwapInverse.genericFourCrossings hg) := by
  have hbc := blockFrobMap_eq_smul_of_eq_on_parity (dataBC d e c z)
    (RealInducedSwapShifted.dataBC d e (RealInducedSwapInverse.genericFourCrossings hg))
    (a := z ^ order c.bc) (fun _ hj => multiplier_eq_scaled_generic hc.1 hz hj)
  have hac := blockFrobMap_eq_smul_of_eq_on_parity (dataAC d e c z)
    (RealInducedSwapShifted.dataAC d e (RealInducedSwapInverse.genericFourCrossings hg))
    (a := z ^ order c.ac) (fun _ hj => multiplier_eq_scaled_generic hc.2.1 hz hj)
  have hbd := blockFrobMap_eq_smul_of_eq_on_parity (dataBD d e c z)
    (RealInducedSwapShifted.dataBD d e (RealInducedSwapInverse.genericFourCrossings hg))
    (a := z ^ order c.bd) (fun _ hj => multiplier_eq_scaled_generic hc.2.2.1 hz hj)
  have had := blockFrobMap_eq_smul_of_eq_on_parity (dataAD d e c z)
    (RealInducedSwapShifted.dataAD d e (RealInducedSwapInverse.genericFourCrossings hg))
    (a := z ^ order c.ad) (fun _ hj => multiplier_eq_scaled_generic hc.2.2.2 hz hj)
  ext f : 1
  simp only [fullMap, RealInducedSwapInverse.fullMap, LinearMap.comp_apply,
    hbc, hac, hbd, had, LinearMap.smul_apply, map_smul, smul_smul,
    totalOrder, pow_add, mul_assoc]
  congr 1
  ring

theorem rawMap_eq_scaled_generic (hc : Valid d e c) {z : ℂ} (hz : z ≠ 0)
    (hg : RealInducedSwapInverse.IsGenericShift d e z) :
    rawMap d e c z = z ^ totalOrder c •
      RealInducedSwapShifted.rawMap d e (RealInducedSwapInverse.genericFourCrossings hg) := by
  rw [RealInducedSwapRegularizedFamily.rawMap, fullMap_eq_scaled_generic d e c hc hz hg]
  rfl

/-- In the simple-pole case division recovers the generic shifted map. -/
theorem normalizedMap_eq_generic (hc : Valid d e c) (horder : totalOrder c = 1)
    {z : ℂ} (hz : z ≠ 0) (hg : RealInducedSwapInverse.IsGenericShift d e z) :
    normalizedMap d e c hc z =
      RealInducedSwapShifted.rawMap d e (RealInducedSwapInverse.genericFourCrossings hg) := by
  rw [normalizedMap, removeSimplePole_of_ne _ _ hz,
    rawMap_eq_scaled_generic d e c hc hz hg, horder, pow_one, smul_smul,
    inv_mul_cancel₀ hz, one_smul]

/-- Vanishing of the residue makes the quotient weakly analytic. -/
theorem normalizedMap_analytic (hc : Valid d e c) (hcan : Cancels d e c)
    (f : KF 4 (source d e)) :
    IsWeaklyAnalyticAt (fun z => normalizedMap d e c hc z f) 0 :=
  weaklyAnalyticAt_removeSimplePole (rawMap d e c) (rawMap_has_derivative d e c hc)
    (rawMap_zero d e c hc hcan) f (rawMap_analytic d e c hc f)

/-- The quotient retains every finite compact degree bound of its source. -/
theorem normalizedMap_mem_layer (hc : Valid d e c) {N : ℕ}
    {f : KF 4 (source d e)}
    (hf : Submodule.inclusion (source_le_expanded d e) f ∈
      layer (realStandardModule 4 (expanded d e)) (degreeLE 4 N)) (z : ℂ) :
    normalizedMap d e c hc z f ∈
      layer (realStandardModule 4 (expanded e d)) (degreeLE 4 N) := by
  let S := layer (realStandardModule 4 (expanded e d)) (degreeLE 4 N)
  have : FiniteDimensional ℂ S :=
    finiteDimensional_layer (fun _ hf => hf.1 :
      realStandardModule 4 (expanded e d) ≤
        principalSeries ℝ 4 (realPositionCharacter (expanded e d))) (degreeLE 4 N)
  exact removeSimplePole_mem (rawMap d e c) (rawMap_has_derivative d e c hc)
    f (rawMap_analytic d e c hc f) S
    (fun z => fullMap_mem_layer d e c z hf) z

theorem normalizedMap_exists_finite_range (hc : Valid d e c)
    (f : KF 4 (source d e)) :
    ∃ S : Submodule ℂ (KF 4 (expanded e d)),
      FiniteDimensional ℂ S ∧ ∀ z, normalizedMap d e c hc z f ∈ S := by
  obtain ⟨S, hS, hfS⟩ := rawMap_exists_finite_range d e c f
  let := hS
  exact ⟨S, hS, removeSimplePole_mem (rawMap d e c)
    (rawMap_has_derivative d e c hc) f (rawMap_analytic d e c hc f) S hfS⟩

end RealInducedSwapRegularization
end Langlands.Archimedean
