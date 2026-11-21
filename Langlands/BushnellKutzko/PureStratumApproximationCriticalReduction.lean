import Langlands.BushnellKutzko.StratumApproximationReduction
import Langlands.BushnellKutzko.MinimalCriticalExponentProof

/-! # Reduction of pure-stratum approximation to the critical level -/

noncomputable section

open ValuativeRel

namespace Langlands.BushnellKutzko

universe uF uV

/-- The witness form of BK93 (2.4.1)(i) restricted to pure strata at their critical level.
On printed p. 71 the computation before (2.4.7) gives the divisibilities. The remark (2.4.7)
records critical-level existence and equivalence with a further conclusion on the derived
stratum, which is not required here. -/
def CriticalPureStratumSimpleApproximationStatement : Prop :=
  ∀ (F : Type uF) [Field F] [ValuativeRel F] [TopologicalSpace F]
    [IsNonarchimedeanLocalField F]
    (V : Type uV) [AddCommGroup V] [Module F V] [FiniteDimensional F V]
    (S : Stratum 𝒪[F] F V), S.IsPure →
      criticalExponent S.chain S.b = ((-S.r : ℤ) : WithBot ℤ) →
      ∃ T : Stratum 𝒪[F] F V,
        T.chain = S.chain ∧ T.n = S.n ∧ T.r = S.r ∧ T.IsSimple ∧ S.Equivalent T ∧
        elementRamificationIndex F T.b ∣ elementRamificationIndex F S.b ∧
        elementResidueDegree F T.b ∣ elementResidueDegree F S.b

/-- The critical-level assertion implies the unrestricted simple approximation assertion.
The opening proof of BK93 (2.4.1)(i), printed p. 66, uses the decrease of `n + k₀`
for finite critical exponents. -/
def PureStratumApproximationCriticalReductionStatement : Prop :=
  CriticalPureStratumSimpleApproximationStatement.{uF, uV} →
    PureStratumSimpleApproximationStatement.{uF, uV}

/-- Prove the critical-level reduction, including preservation of the two divisibilities. -/
theorem pureStratumApproximationCriticalReduction :
    PureStratumApproximationCriticalReductionStatement.{uF, uV} := by
  intro hcrit F _ _ _ _ V _ _ _ S hS
  let height (U : Stratum 𝒪[F] F V) : ℕ :=
    (U.n + WithBot.unbotD (-U.n) (criticalExponent U.chain U.b)).toNat
  suffices H : ∀ (m : ℕ) (U : Stratum 𝒪[F] F V), height U = m → U.IsPure →
      ∃ T : Stratum 𝒪[F] F V,
        T.chain = U.chain ∧ T.n = U.n ∧ T.r = U.r ∧ T.IsSimple ∧ U.Equivalent T ∧
        elementRamificationIndex F T.b ∣ elementRamificationIndex F U.b ∧
        elementResidueDegree F T.b ∣ elementResidueDegree F U.b by
    exact H _ S rfl hS
  intro m
  induction m using Nat.strong_induction_on with
  | _ m ih =>
    intro U hm hU
    by_cases hs : U.IsSimple
    · exact ⟨U, rfl, rfl, rfl, hs, rfl, dvd_rfl, dvd_rfl⟩
    have hkr : ((-U.r : ℤ) : WithBot ℤ) ≤ criticalExponent U.chain U.b :=
      le_of_not_gt fun h => hs ⟨hU, h⟩
    obtain ⟨k, hk⟩ : ∃ k : ℤ, criticalExponent U.chain U.b = (k : WithBot ℤ) := by
      cases h : criticalExponent U.chain U.b with
      | bot => rw [h] at hkr; simp at hkr
      | coe k => exact ⟨k, rfl⟩
    have hle : -U.r ≤ k := WithBot.coe_le_coe.mp (hk ▸ hkr)
    have hrn := U.r_lt_n
    let Uc : Stratum 𝒪[F] F V := ⟨U.chain, U.n, -k, U.b, by omega, U.valuation_ge⟩
    have hkc : criticalExponent Uc.chain Uc.b = ((-Uc.r : ℤ) : WithBot ℤ) := by
      simpa [Uc] using hk
    obtain ⟨G, hGc, hGn, hGr, hG, hUG, he, hf⟩ := hcrit F V Uc hU hkc
    have hGc' : G.chain = U.chain := hGc
    have hGn' : G.n = U.n := hGn
    have hGr' : G.r = -k := hGr
    have hb : U.b - G.b ∈ U.chain.endFiltration k := by
      simpa [Uc] using Stratum.sub_mem_of_equivalent hUG
    have hGk : criticalExponent G.chain G.b < (k : WithBot ℤ) := by
      have h := hG.2
      rwa [hGr', neg_neg] at h
    let W : Stratum 𝒪[F] F V :=
      ⟨G.chain, G.n, U.r, G.b, by rw [hGn']; exact hrn, G.valuation_ge⟩
    have hUW : U.Equivalent W :=
      Stratum.equivalent_of_sub_mem hGc' rfl (U.chain.endFiltration_antitone hle hb)
    by_cases hw : W.IsSimple
    · exact ⟨W, hGc', hGn', rfl, hw, hUW, he, hf⟩
    have hWr : ((-W.r : ℤ) : WithBot ℤ) ≤ criticalExponent W.chain W.b :=
      le_of_not_gt fun h => hw ⟨hG.1, h⟩
    obtain ⟨j, hj⟩ : ∃ j : ℤ, criticalExponent W.chain W.b = (j : WithBot ℤ) := by
      cases h : criticalExponent W.chain W.b with
      | bot => rw [h] at hWr; simp at hWr
      | coe j => exact ⟨j, rfl⟩
    have hj' : criticalExponent G.chain G.b = (j : WithBot ℤ) := hj
    have hjk : j < k := WithBot.coe_lt_coe.mp (hj' ▸ hGk)
    have hjlo : -G.n ≤ j := neg_n_le_criticalExponent minimalCriticalExponent G hG.1 hj'
    have hmW : height W < m := by
      rw [← hm]
      change (G.n + WithBot.unbotD (-G.n) (criticalExponent G.chain G.b)).toNat <
        (U.n + WithBot.unbotD (-U.n) (criticalExponent U.chain U.b)).toNat
      rw [hj', hk]
      simp only [WithBot.unbotD_coe]
      omega
    obtain ⟨T, hTc, hTn, hTr, hT, hWT, hTe, hTf⟩ := ih _ hmW W rfl hG.1
    exact ⟨T, hTc.trans hGc', hTn.trans hGn', hTr, hT, hUW.trans hWT,
      dvd_trans hTe he, dvd_trans hTf hf⟩

end Langlands.BushnellKutzko
