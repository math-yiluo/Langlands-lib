import Langlands.Representation.Archimedean.RealFiniteLayerRegularization
import Langlands.Representation.Archimedean.RealInducedSwapInverse
import Langlands.Representation.Archimedean.RealInducedSwapCancellation

/-!
# Regularized four-crossing families at fixed endpoint exponents

Each of the four explicit scalar multipliers can have one denominator removed.
The resulting ambient family is analytic on every finite compact degree layer.
-/

noncomputable section

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

namespace Langlands.Archimedean
namespace RealInducedSwapRegularizedFamily

open Langlands.LocalFactor.Archimedean
open RealBlockMultiplier RealBlockFrobeniusMap RealCharacterPair
open RealCharacterPairReducible RealInducedSwapGeneric
open RealBlockMultiplierAnalytic RealFiniteLayerRegularization RealKTypeCount
open RealCharacterInducedSwap RealCharacterInducedPushforward

/-- `none` means the generic formula is regular at the center; `some r` removes
the denominator with index `r`, which is required to vanish there. -/
def ValidChoice (ν : ℂ) (ε : ℤ) : Option ℕ → Prop
  | none => ∀ m : ℕ, ν ≠ -((ε : ℂ) + 2 * m + 1)
  | some r => ν = -((ε : ℂ) + 2 * r + 1)

/-- The explicit generic or erased-denominator family, restricted to its parity. -/
def multiplier (ν : ℂ) (ε : ℤ) (c : Option ℕ) (z : ℂ) : ℤ → ℂ :=
  parityRestrict ε (match c with
    | none => genericMultiplier (ν + z) ε
    | some r => regularizedMultiplier (ν + z) ε r)

theorem multiplier_symmetric (ν : ℂ) {ε : ℤ} (hε : ε = 0 ∨ ε = 1)
    (c : Option ℕ) (z : ℂ) :
    IsSymmetric ε ((-1) ^ ε.natAbs) (multiplier ν ε c z) := by
  cases c with
  | none => exact (isSymmetric_genericMultiplier _ hε).parityRestrict
  | some r => exact (isSymmetric_regularizedMultiplier _ hε r).parityRestrict

theorem multiplier_analytic {ν : ℂ} {ε : ℤ} {c : Option ℕ}
    (hc : ValidChoice ν ε c) (j : ℤ) :
    AnalyticAt ℂ (fun z => multiplier ν ε c z j) 0 := by
  apply analyticAt_parityRestrict
  cases c with
  | none =>
    have hseq : ∀ m, AnalyticAt ℂ (fun z => genericSeq z ε m) ν :=
      fun m => analyticAt_genericSeq ε m fun i _ => genericSeq_denom_ne_zero_of_ne hc i
    have hmul : AnalyticAt ℂ (fun z => genericMultiplier z ε j) ν := by
      unfold genericMultiplier extend
      split_ifs
      · exact hseq _
      · exact analyticAt_const.mul (hseq _)
    exact hmul.fun_comp_of_eq (analyticAt_const.add analyticAt_id) (add_zero ν)
  | some r =>
    change ν = -((ε : ℂ) + 2 * r + 1) at hc
    have hm := analyticAt_regularizedMultiplier_at_pole ε j r
    rw [← hc] at hm
    exact hm.fun_comp_of_eq (analyticAt_const.add analyticAt_id) (add_zero ν)

theorem multiplier_recurrent {ν : ℂ} {ε : ℤ} (hε : ε = 0 ∨ ε = 1)
    {c : Option ℕ} (hc : ValidChoice ν ε c) :
    IsRecurrent (ν + 1) ε (multiplier ν ε c 0) := by
  cases c with
  | none =>
    simpa only [multiplier, add_zero] using
      (isRecurrent_genericMultiplier_of_ne hε hc).parityRestrict
  | some r =>
    change ν = -((ε : ℂ) + 2 * r + 1) at hc
    subst ν
    simpa only [multiplier, add_zero] using
      (isRecurrent_regularizedMultiplier_at_pole hε r).parityRestrict

/-- A regularizing choice contributes one power of the parameter. -/
def order : Option ℕ → ℕ
  | none => 0
  | some _ => 1

theorem multiplier_eq_scaled_generic {ν : ℂ} {ε : ℤ} {c : Option ℕ}
    (hc : ValidChoice ν ε c) {z : ℂ} (hz : z ≠ 0) {j : ℤ}
    (hj : Even (j - ε)) :
    multiplier ν ε c z j = z ^ order c * genericMultiplier (ν + z) ε j := by
  unfold multiplier
  rw [parityRestrict_of_even _ hj]
  cases c with
  | none => simp only [order, pow_zero, one_mul]
  | some r =>
    change ν = -((ε : ℂ) + 2 * r + 1) at hc
    have heq : (ε : ℂ) + 2 * r + 1 + (ν + z) = z := by rw [hc]; ring
    change regularizedMultiplier (ν + z) ε r j = z ^ 1 * genericMultiplier (ν + z) ε j
    rw [regularizedMultiplier_eq_mul_genericMultiplier ε r (by rwa [heq]), heq, pow_one]

theorem multiplier_finite_at_positive {ν : ℂ} {ε : ℤ}
    (hε : ε = 0 ∨ ε = 1) (r : ℕ)
    (hν : ν = (ε : ℂ) + 2 * r + 1) :
    RealInducedSwapCancellation.FiniteModes
      (ε.toNat + 2 * r + 1) (multiplier ν ε none 0) := by
  intro j hj
  have he : (ε.toNat : ℤ) = ε := Int.toNat_of_nonneg (by omega)
  have hj' : ε + 2 * (r : ℤ) + 1 ≤ |j| := by
    simpa only [Nat.cast_add, Nat.cast_mul, Nat.cast_ofNat, Nat.cast_one, he] using hj
  simpa only [multiplier, add_zero, hν] using
    parityRestrict_generic_at_positive_finite hε r j hj'

/-- Four independent choices of removed denominators. -/
structure Choices where
  bc : Option ℕ
  ac : Option ℕ
  bd : Option ℕ
  ad : Option ℕ

variable (d e : ComplexCharacterData) (c : Choices)

/-- Each chosen scalar formula is analytic at the center and recurrent there. -/
def Valid : Prop :=
  ValidChoice ((chB d).exponent - (chA e).exponent) (pairParity (chA e) (chB d)) c.bc ∧
  ValidChoice ((chA d).exponent - (chA e).exponent) (pairParity (chA e) (chA d)) c.ac ∧
  ValidChoice ((chB d).exponent - (chB e).exponent) (pairParity (chB e) (chB d)) c.bd ∧
  ValidChoice ((chA d).exponent - (chB e).exponent) (pairParity (chB e) (chA d)) c.ad

section Data

variable {n : ℕ} (pre post : List RealBlock) (x y : RealCharacterData)
    (choice : Option ℕ) (z : ℂ)

/-- Reflection symmetry suffices for the actual Frobenius map at every parameter. -/
theorem crossingData
    (hr : realRank (pre ++ .character x :: .character y :: post) = n) :
    IsBlockFrobData n (pre ++ .character x :: .character y :: post)
      (pre ++ .character y :: .character x :: post) (realRank pre)
      (pairParity y x) (sigma0 y x)
      (multiplier (x.exponent - y.exponent) (pairParity y x) choice z) := by
  simpa only [dc, mid_pair] using
    (data_swap (c := y) (d := x)
      (by simpa only [mid_pair] using realRank_dc_mid hr)
      (multiplier_symmetric (x.exponent - y.exponent) (pairParity_eq y x) choice z))

end Data

theorem dataBC (z : ℂ) : IsBlockFrobData 4 (expanded d e) (crossed d e) 1
    (pairParity (chA e) (chB d)) (sigma0 (chA e) (chB d))
    (multiplier ((chB d).exponent - (chA e).exponent)
      (pairParity (chA e) (chB d)) c.bc z) :=
  crossingData [.character (chA d)] [.character (chB e)]
    (chB d) (chA e) c.bc z rfl

theorem dataAC (z : ℂ) : IsBlockFrobData 4 (crossed d e) (movedLeft d e) 0
    (pairParity (chA e) (chA d)) (sigma0 (chA e) (chA d))
    (multiplier ((chA d).exponent - (chA e).exponent)
      (pairParity (chA e) (chA d)) c.ac z) :=
  crossingData [] [.character (chB d), .character (chB e)]
    (chA d) (chA e) c.ac z rfl

theorem dataBD (z : ℂ) : IsBlockFrobData 4 (movedLeft d e) (middle d e) 2
    (pairParity (chB e) (chB d)) (sigma0 (chB e) (chB d))
    (multiplier ((chB d).exponent - (chB e).exponent)
      (pairParity (chB e) (chB d)) c.bd z) :=
  crossingData [.character (chA e), .character (chA d)] []
    (chB d) (chB e) c.bd z rfl

theorem dataAD (z : ℂ) : IsBlockFrobData 4 (middle d e) (expanded e d) 1
    (pairParity (chB e) (chA d)) (sigma0 (chB e) (chA d))
    (multiplier ((chA d).exponent - (chB e).exponent)
      (pairParity (chB e) (chA d)) c.ad z) :=
  crossingData [.character (chA e)] [.character (chB d)]
    (chA d) (chB e) c.ad z rfl

/-- The explicit four-factor family on the expanded ambient character spaces. -/
def fullMap (z : ℂ) : KF 4 (expanded d e) →ₗ[ℂ] KF 4 (expanded e d) :=
  blockFrobMap (dataAD d e c z) ∘ₗ blockFrobMap (dataBD d e c z) ∘ₗ
    blockFrobMap (dataAC d e c z) ∘ₗ blockFrobMap (dataBC d e c z)

/-- Restrict the source to its actual two induction windows. -/
def rawMap (z : ℂ) : KF 4 (source d e) →ₗ[ℂ] KF 4 (expanded e d) :=
  fullMap d e c z ∘ₗ Submodule.inclusion (source_le_expanded d e)

theorem fullMap_mem_layer (z : ℂ) {N : ℕ} {f : KF 4 (expanded d e)}
    (hf : f ∈ layer (realStandardModule 4 (expanded d e)) (degreeLE 4 N)) :
    fullMap d e c z f ∈ layer (realStandardModule 4 (expanded e d)) (degreeLE 4 N) :=
  mem_layer_blockFrobMap (dataAD d e c z) (mem_layer_blockFrobMap (dataBD d e c z)
    (mem_layer_blockFrobMap (dataAC d e c z) (mem_layer_blockFrobMap (dataBC d e c z) hf)))

theorem fullMap_analytic (hc : Valid d e c)
    {N : ℕ} {f : ℂ → KF 4 (expanded d e)}
    (hf : ∀ z, f z ∈ layer (realStandardModule 4 (expanded d e)) (degreeLE 4 N))
    (ha : IsWeaklyAnalyticAt f 0) :
    IsWeaklyAnalyticAt (fun z => fullMap d e c z (f z)) 0 := by
  have h₁ := weaklyAnalyticAt_blockFrobMap (dataBC d e c) hf ha
    (multiplier_analytic hc.1)
  have h₂ := weaklyAnalyticAt_blockFrobMap (dataAC d e c)
    (fun z => mem_layer_blockFrobMap (dataBC d e c z) (hf z)) h₁
    (multiplier_analytic hc.2.1)
  have h₃ := weaklyAnalyticAt_blockFrobMap (dataBD d e c)
    (fun z => mem_layer_blockFrobMap (dataAC d e c z)
      (mem_layer_blockFrobMap (dataBC d e c z) (hf z)))
    h₂ (multiplier_analytic hc.2.2.1)
  exact weaklyAnalyticAt_blockFrobMap (dataAD d e c)
    (fun z => mem_layer_blockFrobMap (dataBD d e c z)
      (mem_layer_blockFrobMap (dataAC d e c z)
        (mem_layer_blockFrobMap (dataBC d e c z) (hf z))))
    h₃ (multiplier_analytic hc.2.2.2)

theorem rawMap_analytic (hc : Valid d e c) (f : KF 4 (source d e)) :
    IsWeaklyAnalyticAt (fun z => rawMap d e c z f) 0 := by
  obtain ⟨N, hN⟩ := exists_mem_layer_degreeLE
    (fun _ hf => hf.1 : realStandardModule 4 (expanded d e) ≤
      principalSeries ℝ 4 (realPositionCharacter (expanded d e)))
    (Submodule.inclusion (source_le_expanded d e) f)
  exact fullMap_analytic d e c hc (fun _ => hN) (IsWeaklyAnalyticAt.const _ 0)

theorem rawMap_exists_finite_range (f : KF 4 (source d e)) :
    ∃ S : Submodule ℂ (KF 4 (expanded e d)),
      FiniteDimensional ℂ S ∧ ∀ z, rawMap d e c z f ∈ S := by
  obtain ⟨N, hN⟩ := exists_mem_layer_degreeLE
    (fun _ hf => hf.1 : realStandardModule 4 (expanded d e) ≤
      principalSeries ℝ 4 (realPositionCharacter (expanded d e)))
    (Submodule.inclusion (source_le_expanded d e) f)
  refine ⟨layer (realStandardModule 4 (expanded e d)) (degreeLE 4 N), ?_,
    fun z => fullMap_mem_layer d e c z hN⟩
  exact finiteDimensional_layer (fun _ hf => hf.1 :
    realStandardModule 4 (expanded e d) ≤
      principalSeries ℝ 4 (realPositionCharacter (expanded e d))) (degreeLE 4 N)

/-- The derivative vectors required by the linear simple-pole construction exist. -/
theorem rawMap_has_derivative (hc : Valid d e c) (f : KF 4 (source d e)) :
    ∃ v, HasWeakDerivAt (fun z => rawMap d e c z f) v 0 := by
  obtain ⟨S, hS, hfS⟩ := rawMap_exists_finite_range d e c f
  let := hS
  obtain ⟨v, _, hv⟩ := exists_weakDerivAt_mem (rawMap_analytic d e c hc f) S hfS
  exact ⟨v, hv⟩

/-- The candidate normalized value is the derivative of the regularized family. -/
def normalizedMap (hc : Valid d e c) (z : ℂ) :
    KF 4 (source d e) →ₗ[ℂ] KF 4 (expanded e d) :=
  removeSimplePole (rawMap d e c) (rawMap_has_derivative d e c hc) z

/-- At the center all four scalar sequences are recurrent. -/
def atZero (hc : Valid d e c) : RealInducedSwapRecurrent.FourCrossings d e where
  bc := ⟨multiplier _ _ c.bc 0,
    multiplier_symmetric _ (pairParity_eq _ _) c.bc 0,
    multiplier_recurrent (pairParity_eq _ _) hc.1⟩
  ac := ⟨multiplier _ _ c.ac 0,
    multiplier_symmetric _ (pairParity_eq _ _) c.ac 0,
    multiplier_recurrent (pairParity_eq _ _) hc.2.1⟩
  bd := ⟨multiplier _ _ c.bd 0,
    multiplier_symmetric _ (pairParity_eq _ _) c.bd 0,
    multiplier_recurrent (pairParity_eq _ _) hc.2.2.1⟩
  ad := ⟨multiplier _ _ c.ad 0,
    multiplier_symmetric _ (pairParity_eq _ _) c.ad 0,
    multiplier_recurrent (pairParity_eq _ _) hc.2.2.2⟩

set_option maxHeartbeats 1000000 in
theorem rawMap_zero_eq_recurrent (hc : Valid d e c) :
    rawMap d e c 0 = RealInducedSwapRecurrent.rawMap d e (atZero d e c hc) := by
  ext f : 1
  rfl

end RealInducedSwapRegularizedFamily
end Langlands.Archimedean
