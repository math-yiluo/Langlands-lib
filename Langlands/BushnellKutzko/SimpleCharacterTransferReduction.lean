import Langlands.BushnellKutzko.SimpleCharacterTransferStatement
import Langlands.BushnellKutzko.SimpleCharacterTransferInputs
import Langlands.BushnellKutzko.SimpleCharacterTransferDepth
import Langlands.BushnellKutzko.SimpleCharacterTransferTerminal

/-! # Reduction of simple-character transfer to approximation and character restriction -/

open ValuativeRel

noncomputable section

namespace Langlands.BushnellKutzko

universe uF uV

/-- The transfer assertion follows from pure-stratum approximation, the
subgroup properties, the critical twist and the independence of defining sequences. -/
def SimpleCharacterTransferReductionStatement : Prop :=
  PureStratumSimpleApproximationStatement.{uF, uV} →
  SimpleStratumGroupPropertiesStatement.{uF, uV} →
  SimpleCharacterRestrictionStatement.{uF, uV} →
  SimpleCharacterChoiceStatement.{uF, uV} →
  SimpleCharacterTransferStatement.{uF, uV}

section Transfer

variable {F : Type uF} [Field F] [ValuativeRel F] [TopologicalSpace F]
  [IsNonarchimedeanLocalField F] {V : Type uV} [AddCommGroup V] [Module F V]

private abbrev TransferOn (ψF : AddChar F ℂ) (L M : LatticeChain 𝒪[F] F V)
    (n₁ n₂ : ℤ) (β γ : Module.End F V) (tail₁ tail₂ : List (Module.End F V)) (m₁ m₂ : ℕ) : Prop :=
  ∀ θ₁ ∈ simpleCharacters ψF L n₁ β tail₁ m₁,
    ∃! θ₂, θ₂ ∈ simpleCharacters ψF M n₂ γ tail₂ m₂ ∧
      characterAgreesOn (simpleHGroup L n₁ β tail₁ (m₁ + 1) ⊓
        simpleHGroup M n₂ γ tail₂ (m₂ + 1)) θ₁ θ₂ (fun _ => 1)

private abbrev TransferAt (ψF : AddChar F ℂ) (S T : Stratum 𝒪[F] F V) (m₁ m₂ : ℕ)
    (q : S.DefiningSequenceChoice) (q' : T.DefiningSequenceChoice) : Prop :=
  TransferOn ψF S.chain T.chain S.n T.n S.b T.b q.tail q'.tail m₁ m₂

private abbrev transferMeasure (S : Stratum 𝒪[F] F V) : ℕ :=
  (S.n - finiteCriticalDepth S.chain S.n S.b).toNat

private theorem derived_of_criticalApproximation {S T : Stratum 𝒪[F] F V}
    (hS : S.IsPure) (hT : S.IsCriticalApproximation T) (hc : T.chain = S.chain) :
    T.HasSimpleDerivedStratum (S.b - T.b) := by
  let := S.chain.finiteDimensional
  obtain ⟨_, hn, hsimple, hk, hcongr⟩ := hT
  let R : Stratum 𝒪[F] F V := { S with r := T.r, r_lt_n := hn ▸ T.r_lt_n }
  have hEq : R.Equivalent T :=
    Stratum.equivalent_of_sub_mem hc rfl (by simpa using neg_mem hcongr)
  exact criticalDerivedStratum F V R T hS hk hc hn rfl hsimple hEq

end Transfer

set_option maxHeartbeats 2400000 in
set_option synthInstance.maxHeartbeats 200000 in
/-- Prove the transfer assertion by induction on the distance of the critical
cutoff from the initial level. -/
theorem simpleCharacterTransferReduction : SimpleCharacterTransferReductionStatement.{uF, uV} := by
  intro hApprox hGroup hRestrict hChoice F _ _ _ _ V _ _ ψF hψ
  suffices h : ∀ (d : ℕ) (S T : Stratum 𝒪[F] F V) (m₁ m₂ : ℕ),
      S.b = T.b → S.r = m₁ → T.r = m₂ → S.IsSimple → T.IsSimple → transferMeasure S = d →
      ∀ (q : S.DefiningSequenceChoice) (q' : T.DefiningSequenceChoice),
        m₁ / (S.chain.period / elementRamificationIndex F S.b) =
          m₂ / (T.chain.period / elementRamificationIndex F S.b) →
          TransferAt ψF S T m₁ m₂ q q' from
    fun S T m₁ m₂ hst hrs hrt hs ht q q' hm => h _ S T m₁ m₂ hst hrs hrt hs ht rfl q q' hm
  intro d
  induction d using Nat.strong_induction_on with
  | _ d ih =>
    intro S T m₁ m₂ hst hrs hrt hs ht hd q q' hm
    obtain ⟨L, n₁, s, β, hslt, hsval⟩ := S
    obtain ⟨M, n₂, t, β', htlt, htval⟩ := T
    dsimp only at hst hrs hrt
    subst β'
    subst s
    subst t
    let S : Stratum 𝒪[F] F V := ⟨L, n₁, m₁, β, hslt, hsval⟩
    let T : Stratum 𝒪[F] F V := ⟨M, n₂, m₂, β, htlt, htval⟩
    have hS : S.IsSimple := hs
    have hT : T.IsSimple := ht
    change (m₁ : ℤ) < n₁ at hslt
    change (m₂ : ℤ) < n₂ at htlt
    change m₁ / (L.period / elementRamificationIndex F β) =
      m₂ / (M.period / elementRamificationIndex F β) at hm
    have h0S : 0 ≤ S.r := Int.natCast_nonneg m₁
    have h0T : 0 ≤ T.r := Int.natCast_nonneg m₂
    obtain ⟨hf, hL⟩ := hS.1.1
    obtain ⟨_, hM⟩ := hT.1.1
    have hv₁ : L.valuation β = ((-n₁ : ℤ) : WithTop ℤ) := hS.1.2
    have hv₂ : M.valuation β = ((-n₂ : ℤ) : WithTop ℤ) := hT.1.2
    by_cases hstop : criticalExponent L β = ((-n₁ : ℤ) : WithBot ℤ) ∨ criticalExponent L β = ⊥
    · have hstop' : criticalExponent M β = ((-n₂ : ℤ) : WithBot ℤ) ∨ criticalExponent M β = ⊥ := by
        by_contra hnot
        obtain ⟨r, hkr, hr⟩ := exists_nonterminal_criticalDepth T hT hnot
        obtain ⟨_, W, _, _, _, _, hWn, _, _, _, _, _, hWk, _, _, _, _, _⟩ :=
          exists_common_critical_approximation hApprox M L n₂ n₁ β r hf hM hL hv₂ hv₁ hkr hr
        rcases hstop with hfin | hbot
        · have hEq := WithBot.coe_injective (hWk.symm.trans hfin)
          have hw := W.r_lt_n
          omega
        · exact WithBot.bot_ne_coe (hbot.symm.trans hWk)
      change TransferAt ψF S T m₁ m₂ q q'
      unfold TransferAt
      rw [q.tail_eq_nil_of_terminal hstop, q'.tail_eq_nil_of_terminal hstop']
      exact simpleCharacterTransfer_nil ψF hψ L M n₁ n₂ β m₁ m₂ hslt htlt hv₁ hv₂ hf hL hM hm
    obtain ⟨r, hkr, hr⟩ := exists_nonterminal_criticalDepth S hS hstop
    obtain ⟨U, W, r₀, hUc, hWc, hUn, hWn, _, hUW, hU, hW, hkL, hkM, hcongrL, hcongrM, hscaleL, hscaleM, hram⟩ :=
      exists_common_critical_approximation hApprox L M n₁ n₂ β r hf hL hM hv₁ hv₂ hkr hr
    have hCritL : S.IsCriticalApproximation U := ⟨by rw [hUc], hUn, hU, hkL, hcongrL⟩
    have hCritM : T.IsCriticalApproximation W := ⟨by rw [hWc], hWn, hW, hkM, hcongrM⟩
    have hrL : finiteCriticalDepth L n₁ β = U.r := finiteCriticalDepth_eq_of_criticalExponent _ _ _ _ hkL
    have hrM : finiteCriticalDepth M n₂ β = W.r := finiteCriticalDepth_eq_of_criticalExponent _ _ _ _ hkM
    have hmL : (m₁ : ℤ) < U.r := by
      have h := hS.2
      change criticalExponent L β < ((-(m₁ : ℤ) : ℤ) : WithBot ℤ) at h
      rw [hkL] at h
      have hh := WithBot.coe_lt_coe.mp h
      omega
    have hmM : (m₂ : ℤ) < W.r := by
      have h := hT.2
      change criticalExponent M β < ((-(m₂ : ℤ) : ℤ) : WithBot ℤ) at h
      rw [hkM] at h
      have hh := WithBot.coe_lt_coe.mp h
      omega
    let j₁ := max m₁ (finiteCriticalDepth L n₁ β / 2).toNat
    let j₂ := max m₂ (finiteCriticalDepth M n₂ β / 2).toNat
    have hjL₁ : U.r / 2 ≤ (j₁ : ℤ) := by dsimp only [j₁]; rw [hrL]; omega
    have hjM₁ : W.r / 2 ≤ (j₂ : ℤ) := by dsimp only [j₂]; rw [hrM]; omega
    have hjL₂ : (j₁ : ℤ) < U.r := by dsimp only [j₁]; rw [hrL]; omega
    have hjM₂ : (j₂ : ℤ) < W.r := by dsimp only [j₂]; rw [hrM]; omega
    obtain ⟨he, hperL⟩ := elementRamification_period_factorization L β hf hL
    obtain ⟨_, hperM⟩ := elementRamification_period_factorization M β hf hM
    have hperpos {p : ℕ} (hp : 0 < p) (h : p = elementRamificationIndex F β * (p / elementRamificationIndex F β)) :
        0 < p / elementRamificationIndex F β := by
      by_contra! hz
      rw [Nat.eq_zero_of_le_zero hz, mul_zero] at h
      exact hp.ne' h
    have hposL := hperpos L.period_pos hperL
    have hposM := hperpos M.period_pos hperM
    have hr₀ : 0 ≤ r₀ := by
      by_contra! hneg
      have hh := mul_neg_of_pos_of_neg (show (0 : ℤ) < ((L.period / elementRamificationIndex F β : ℕ) : ℤ) by
        exact_mod_cast hposL) hneg
      rw [← hscaleL] at hh
      omega
    have hjNorm : j₁ / (L.period / elementRamificationIndex F β) = j₂ / (M.period / elementRamificationIndex F β) := by
      have hscaleL' : U.r = ((L.period / elementRamificationIndex F β : ℕ) : ℤ) * (r₀.toNat : ℤ) := by
        rwa [Int.toNat_of_nonneg hr₀]
      have hscaleM' : W.r = ((M.period / elementRamificationIndex F β : ℕ) : ℤ) * (r₀.toNat : ℤ) := by
        rwa [Int.toNat_of_nonneg hr₀]
      dsimp only [j₁, j₂]
      rw [hrL, hrM, normalized_max_half_div _ hposL hscaleL', normalized_max_half_div _ hposM hscaleM', hm]
    have hjNext : j₁ / (L.period / elementRamificationIndex F U.b) = j₂ / (M.period / elementRamificationIndex F U.b) :=
      normalized_depth_eq_of_ramification_dvd he hram hperL hperM hjNorm
    obtain ⟨qU, hqU₀, _⟩ := Stratum.exists_exact_definingSequenceChoice hApprox U hU
    obtain ⟨qW, hqW₀, _⟩ := Stratum.exists_exact_definingSequenceChoice hApprox W hW
    have hderL := derived_of_criticalApproximation hS.1 hCritL hUc
    have hderM := derived_of_criticalApproximation hT.1 hCritM hWc
    let qS := qU.prepend hS hCritL hqU₀ hderL
    let qT := qW.prepend hT hCritM hqW₀ hderM
    have hqS : qS.tail = U.b :: qU.tail := qU.prepend_tail hS hCritL hqU₀ hderL
    have hqT : qT.tail = U.b :: qW.tail := by
      rw [hUW]
      exact qW.prepend_tail hT hCritM hqW₀ hderM
    let U' := U.lowerIndex (j₁ : ℤ) hjL₂.le
    let W' := W.lowerIndex (j₂ : ℤ) hjM₂.le
    have hDec : transferMeasure U' < d := by
      change transferMeasure U < d
      exact (critical_transfer_measure_lt hCritL).trans_eq hd
    have hNextNorm : j₁ / (U'.chain.period / elementRamificationIndex F U'.b) =
        j₂ / (W'.chain.period / elementRamificationIndex F U'.b) := by
      change j₁ / (U.chain.period / elementRamificationIndex F U.b) =
        j₂ / (W.chain.period / elementRamificationIndex F U.b)
      rwa [hUc, hWc]
    have hNext := ih _ hDec U' W' j₁ j₂ hUW rfl rfl (hU.lowerIndex hjL₂.le) (hW.lowerIndex hjM₂.le)
      rfl (qU.lowerIndex hjL₂.le) (qW.lowerIndex hjM₂.le) hNextNorm
    change TransferOn ψF U.chain W.chain U.n W.n U.b W.b
      (qU.lowerIndex hjL₂.le).tail (qW.lowerIndex hjM₂.le).tail j₁ j₂ at hNext
    rw [qU.lowerIndex_tail hjL₂.le, qW.lowerIndex_tail hjM₂.le, hUc, hWc, hUn, hWn, ← hUW] at hNext
    have hnonL : elementAlgebra β ≠ ⊥ := by
      intro h
      simp [criticalExponent, h] at hkL
    have hgrpL := transfer_group_properties hGroup S h0S hS qS m₁ hnonL (by simpa only [S, hrL] using hmL)
    have hgrpM := transfer_group_properties hGroup T h0T hT qT m₂ hnonL (by simpa only [T, hrM] using hmM)
    have htwL := transfer_critical_twist hRestrict ψF hψ S U h0S hS qS hCritL qU j₁
      (by simpa only [S, hrL] using hjL₁) (by simpa only [S, hrL] using hjL₂)
    have htwM := transfer_critical_twist hRestrict ψF hψ T W h0T hT qT hCritM qW j₂
      (by simpa only [T, hrM] using hjM₁) (by simpa only [T, hrM] using hjM₂)
    dsimp only [S] at hgrpL htwL
    dsimp only [T] at hgrpM htwM
    rw [hqS] at hgrpL htwL
    rw [hqT] at hgrpM htwM
    rw [hUc, hUn] at htwL
    rw [hWc, hWn, ← hUW] at htwM
    have hjMfinite : (j₂ : ℤ) < finiteCriticalDepth M n₂ β := by rwa [hrM]
    have hCanonical : TransferAt ψF S T m₁ m₂ qS qT := by
      unfold TransferAt
      rw [hqS, hqT]
      exact simpleCharacterTransfer_cons_of_transfer_next ψF L M n₁ n₂ β U.b qU.tail qW.tail m₁ m₂ hf hL hM hm
        (hrL.symm ▸ hmL) (hrM.symm ▸ hmM) hjMfinite hjNorm
        hgrpL.1 hgrpM.1 hgrpM.2.1 hgrpM.2.2 htwL.1 htwM.1 htwM.2 hNext
    obtain ⟨hH₁, hC₁⟩ := transfer_choice_comparison hChoice ψF hψ S h0S hS q qS m₁ hslt
    obtain ⟨hH₂, hC₂⟩ := transfer_choice_comparison hChoice ψF hψ T h0T hT q' qT m₂ htlt
    exact transfer_of_choice hH₁ hH₂ hC₁ hC₂ hCanonical

end Langlands.BushnellKutzko
