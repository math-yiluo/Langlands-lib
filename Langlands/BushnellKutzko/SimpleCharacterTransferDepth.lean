import Langlands.BushnellKutzko.SimpleCharacterTransferApproximation
import Langlands.BushnellKutzko.SimpleCharacterTransferSequences

/-! # Relative indices and a decreasing measure for transfer -/

open ValuativeRel

noncomputable section

namespace Langlands.BushnellKutzko

universe uF uV

variable {F : Type uF} [Field F] [ValuativeRel F] [TopologicalSpace F]
  [IsNonarchimedeanLocalField F] {V : Type uV} [AddCommGroup V] [Module F V]

local notation "A" => Module.End F V

omit [TopologicalSpace F] [IsNonarchimedeanLocalField F] in
/-- On a finite critical exponent, the integer critical depth is its negative. -/
theorem finiteCriticalDepth_eq_of_criticalExponent (L : LatticeChain 𝒪[F] F V)
    (n : ℤ) (β : A) (r : ℤ) (h : criticalExponent L β = ((-r : ℤ) : WithBot ℤ)) :
    finiteCriticalDepth L n β = r := by
  simp [finiteCriticalDepth, simpleCriticalDepth, h]

/-- A nonterminal simple stratum has finite critical depth strictly below its level. -/
theorem exists_nonterminal_criticalDepth (S : Stratum 𝒪[F] F V) (hS : S.IsSimple)
    (h : ¬ (criticalExponent S.chain S.b = ((-S.n : ℤ) : WithBot ℤ) ∨
      criticalExponent S.chain S.b = ⊥)) :
    ∃ r : ℤ, criticalExponent S.chain S.b = ((-r : ℤ) : WithBot ℤ) ∧ r < S.n := by
  let := S.chain.finiteDimensional
  cases hk : criticalExponent S.chain S.b with
  | bot => exact (h (.inr hk)).elim
  | coe k =>
      have hlow := neg_n_le_criticalExponent minimalCriticalExponent S hS.1 hk
      have hne : k ≠ -S.n := fun he => h (.inl (hk.trans (by rw [he])))
      exact ⟨-k, by simp, by omega⟩

omit [TopologicalSpace F] [IsNonarchimedeanLocalField F] in
/-- The distance from the finite critical cutoff to the initial level decreases
under critical approximation, with the initial level used for a scalar. -/
theorem critical_transfer_measure_lt {S T : Stratum 𝒪[F] F V}
    (hT : S.IsCriticalApproximation T) :
    (T.n - finiteCriticalDepth T.chain T.n T.b).toNat <
      (S.n - finiteCriticalDepth S.chain S.n S.b).toNat := by
  obtain ⟨_, hn, hsimple, hk, _⟩ := hT
  have hlt := T.r_lt_n
  rw [finiteCriticalDepth_eq_of_criticalExponent _ _ _ _ hk, ← hn]
  cases h : criticalExponent T.chain T.b with
  | bot =>
      simp [finiteCriticalDepth, simpleCriticalDepth, h]
      omega
  | coe k =>
      have hsimple' := hsimple.2
      rw [h] at hsimple'
      have hkr := WithBot.coe_lt_coe.mp hsimple'
      rw [finiteCriticalDepth_eq_of_criticalExponent T.chain T.n T.b (-k) (by rwa [neg_neg])]
      omega

/-- The base period is the ramification index times the relative period
computed by natural division. -/
theorem elementRamification_period_factorization (L : LatticeChain 𝒪[F] F V)
    (β : A) (hf : IsField (elementAlgebra β))
    (hL : letI := hf.toField
      ∀ a : (elementAlgebra β)ˣ, subfieldUnits F (elementAlgebra β) V a ∈ L.stabilizer) :
    0 < elementRamificationIndex F β ∧
    L.period = elementRamificationIndex F β * (L.period / elementRamificationIndex F β) := by
  let := hf.toField
  obtain ⟨D, _, _, _, _, _, hprod⟩ := subfieldOrder F V (elementAlgebra β) L hL
  have hpos : 0 < subfieldRamificationIndex F (elementAlgebra β) := by
    by_contra! h
    rw [Nat.eq_zero_of_le_zero h, zero_mul] at hprod
    exact L.period_pos.ne' hprod
  simp only [elementRamificationIndex, hf, dite_true]
  refine ⟨hpos, ?_⟩
  rw [hprod, Nat.mul_div_cancel_left _ hpos]

/-- Changing the ramification index to a divisor preserves equality of the
normalized depths. -/
theorem normalized_depth_eq_of_ramification_dvd {p₁ p₂ e f j₁ j₂ : ℕ}
    (he : 0 < e) (hf : f ∣ e)
    (hp₁ : p₁ = e * (p₁ / e)) (hp₂ : p₂ = e * (p₂ / e))
    (hj : j₁ / (p₁ / e) = j₂ / (p₂ / e)) : j₁ / (p₁ / f) = j₂ / (p₂ / f) := by
  obtain ⟨a, ha⟩ := hf
  have hf' : 0 < f := by
    by_contra! h
    rw [Nat.eq_zero_of_le_zero h, zero_mul] at ha
    exact he.ne' ha
  have hdiv {p : ℕ} (hp : p = e * (p / e)) : p / f = (p / e) * a := by
    calc p / f = (e * (p / e)) / f := congrArg (· / f) hp
      _ = (p / e) * a := by
        have hd : e * (p / e) = f * (a * (p / e)) := by rw [← Nat.mul_assoc, ← ha]
        rw [hd, Nat.mul_div_cancel_left _ hf', Nat.mul_comm a]
  rw [hdiv hp₁, hdiv hp₂, ← Nat.div_div_eq_div_mul, ← Nat.div_div_eq_div_mul, hj]

end Langlands.BushnellKutzko
