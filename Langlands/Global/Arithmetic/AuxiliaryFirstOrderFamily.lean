import Langlands.Global.Arithmetic.AuxiliaryFirstOrderHelpers
import Langlands.HarmonicAnalysis.PadicDeepUnitCharacterProof
import Langlands.HarmonicAnalysis.PadicPrincipalUnitCharacterExtensionProof

/-! One fixed conductor offset gives first-order finite characters at every level. -/

noncomputable section

namespace Langlands.Global.AuxiliaryFirstOrder

universe u

private theorem prime_ne_zero {p : ℕ} [Fact p.Prime]
    {F : PadicField.{u} p} (T : F.TopologicalData) : (p : F.Carrier) ≠ 0 := by
  intro h
  have he := T.ord_prime_pos
  rw [h, T.ord_zero] at he
  omega

/-- The exact normalized valuation of every integer power of the rational prime. -/
theorem valuation_prime_zpow {p : ℕ} [Fact p.Prime]
    {F : PadicField.{u} p} (T : F.TopologicalData) (z : ℤ) :
    T.discreteValuation ((p : F.Carrier) ^ z) =
      WithZero.exp (-z * T.ord (p : F.Carrier)) := by
  have hn : T.discreteValuation ((p : F.Carrier) ^ z) ≠ 0 :=
    T.discreteValuation.ne_zero_iff.mpr (zpow_ne_zero _ (prime_ne_zero T))
  calc
    _ = WithZero.exp (-T.ord ((p : F.Carrier) ^ z)) := by
      simp only [PadicField.TopologicalData.ord, neg_neg]
      exact (WithZero.exp_log hn).symm
    _ = _ := by rw [T.ord_zpow]; congr 1; ring

/-- A fixed offset makes the quadratic error small at every increasing first-order level. -/
theorem exists_first_order_family {p : ℕ} [Fact p.Prime]
    (F : PadicField.{u} p) (T : F.TopologicalData) :
    letI := T.topology
    ∀ ψ : HarmonicAnalysis.UnitaryAdditiveCharacter F.Carrier,
      ∃ C : ℕ, ∀ k : ℕ,
        let c : F.Carrier := (p : F.Carrier) ^ ((C : ℤ) - 2 * (k : ℤ))
        let n : ℕ := k * T.ramificationIndex
        ∃ χ : F.Carrierˣ →ₜ* ℂˣ,
          (∃ m : ℕ, 0 < m ∧ χ ^ m = 1) ∧
          (∀ z : T.principalUnits n,
            χ (z : F.Carrierˣ) = Circle.toUnits
              (ψ (c * (((z : F.Carrierˣ) : F.Carrier) - 1)))) ∧
          T.discreteValuation c * T.discreteValuation ((p : F.Carrier) ^ k) ^ 2 ≤
            WithZero.exp (T.additiveConductor ψ) ∧
          T.discreteValuation ((p : F.Carrier) ^ k) = WithZero.exp (-(n : ℤ)) ∧
          (0 < k → T.discreteValuation ((p : F.Carrier) ^ k) < 1) := by
  let := T.topology
  intro ψ
  let C : ℕ := (-T.additiveConductor ψ).toNat
  have he : 1 ≤ T.ord (p : F.Carrier) := T.ord_prime_pos
  have hC : -(C : ℤ) * T.ord (p : F.Carrier) ≤ T.additiveConductor ψ := by
    have hCe : (C : ℤ) ≤ (C : ℤ) * T.ord (p : F.Carrier) := by
      nlinarith [Int.natCast_nonneg C]
    have hc : -T.additiveConductor ψ ≤ (C : ℤ) := Int.self_le_toNat _
    nlinarith
  refine ⟨C, fun k => ?_⟩
  let c : F.Carrier := (p : F.Carrier) ^ ((C : ℤ) - 2 * (k : ℤ))
  let n : ℕ := k * T.ramificationIndex
  have hn : (n : ℤ) = (k : ℤ) * T.ord (p : F.Carrier) := by
    simp only [n, Nat.cast_mul, T.ramificationIndex_cast]
  have hcval : T.discreteValuation c =
      WithZero.exp (-((C : ℤ) - 2 * (k : ℤ)) * T.ord (p : F.Carrier)) :=
    valuation_prime_zpow T _
  have ha : T.discreteValuation ((p : F.Carrier) ^ k) = WithZero.exp (-(n : ℤ)) := by
    rw [← zpow_natCast, valuation_prime_zpow, hn]
    congr 1
    ring
  have hquad : T.discreteValuation c * WithZero.exp (-(2 * (n : ℤ))) ≤
      WithZero.exp (T.additiveConductor ψ) := by
    rw [hcval, ← WithZero.exp_add]
    apply WithZero.exp_le_exp.mpr
    rw [hn]
    nlinarith
  obtain ⟨η, hη, _⟩ := HarmonicAnalysis.padicDeepUnitCharacter p F T ψ c n hquad
  let circleUnits : Circle →ₜ* ℂˣ :=
    { toMonoidHom := Circle.toUnits
      continuous_toFun := Continuous.of_coeHom_comp continuous_subtype_val }
  obtain ⟨χ, hfin, hχ, _⟩ :=
    HarmonicAnalysis.padicPrincipalUnitCharacterExtension p F T n (circleUnits.comp η)
  refine ⟨χ, hfin, ?_, ?_, ha, ?_⟩
  · intro z
    rw [hχ]
    exact congrArg Circle.toUnits (hη z)
  · rw [ha, ← WithZero.exp_nsmul, nsmul_eq_mul]
    convert hquad using 1
    congr 2
    ring
  · intro hk
    rw [ha, ← WithZero.exp_zero]
    apply WithZero.exp_lt_exp.mpr
    have hnpos : 0 < n := Nat.mul_pos hk T.ramificationIndex_pos
    omega

end Langlands.Global.AuxiliaryFirstOrder
