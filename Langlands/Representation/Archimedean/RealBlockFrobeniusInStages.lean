import Langlands.Representation.Archimedean.RealAmbientCanonicalCharacterBraid
import Langlands.Representation.Archimedean.RealInjectiveIntertwinerStages

/-! # Frobenius data and maps in a consecutive block slice -/

noncomputable section

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

namespace Langlands.Archimedean.RealBlockFrobeniusMap

open Langlands.LocalFactor.Archimedean
open RealBlockPosition RealBlockJacquet RealStandardFiltration

variable {n r p : ℕ} {pre post ds es : List RealBlock}
  {ε : ℤ} {σ : ℂ} {μ : ℤ → ℂ}

private theorem outside_or_mid (a r i : ℕ) :
    (i < a ∨ a + r ≤ i) ∨ ∃ j < r, i = a + j := by
  by_cases h : i < a ∨ a + r ≤ i
  · exact Or.inl h
  · exact Or.inr ⟨i - a, by omega, by omega⟩

/-- Frobenius data in a consecutive slice extend through equal surrounding
blocks, keeping the multiplier and translating its rotation position. -/
theorem IsBlockFrobData.inStages (h : IsBlockFrobData r ds es p ε σ μ)
    (hd : realRank ds = r) (hn : realRank (pre ++ es ++ post) = n) :
    IsBlockFrobData n (pre ++ ds ++ post) (pre ++ es ++ post) (realRank pre + p) ε σ μ := by
  have he := h.rank
  have hr : realRank es = realRank ds := he.trans hd.symm
  have hpn : p < r := by have := h.lt; omega
  have hqn := h.lt
  have ha : realRank pre + r ≤ n := by
    simp only [InductionStages.realRank_append', he] at hn
    omega
  have hpd : p < realRank ds := hd.symm ▸ hpn
  have hpe : p < realRank es := he.symm ▸ hpn
  have hqd : p + 1 < realRank ds := hd.symm ▸ hqn
  have hqe : p + 1 < realRank es := he.symm ▸ hqn
  refine
    { lt := by omega
      rank := hn
      sign_off := ?_
      exp_off := ?_
      exp_p := ?_
      exp_q := ?_
      par := ?_
      sym := h.sym
      sign_p := ?_
      sign_q := ?_
      induced_off := ?_
      induced_p := ?_ }
  · intro i hi hi'
    rcases outside_or_mid (realRank pre) r i with hout | ⟨j, hj, rfl⟩
    · exact realPositionSign_of_not_mid hr (by simpa only [he] using hout)
    · rw [realPositionSign_mid pre es post (he.symm ▸ hj),
        realPositionSign_mid pre ds post (hd.symm ▸ hj)]
      exact h.sign_off j (by omega) (by omega)
  · intro i hi hi'
    rcases outside_or_mid (realRank pre) r i with hout | ⟨j, hj, rfl⟩
    · exact realPositionExponent_of_not_mid hr (by simpa only [he] using hout)
    · rw [realPositionExponent_mid pre es post (he.symm ▸ hj),
        realPositionExponent_mid pre ds post (hd.symm ▸ hj)]
      exact h.exp_off j (by omega) (by omega)
  · rw [Nat.add_assoc, realPositionExponent_mid pre es post hpe,
      realPositionExponent_mid pre ds post hqd]
    exact h.exp_p
  · rw [Nat.add_assoc, realPositionExponent_mid pre es post hqe,
      realPositionExponent_mid pre ds post hpd]
    exact h.exp_q
  · rw [Nat.add_assoc, realPositionCharacter_mid pre ds post hpd,
      realPositionCharacter_mid pre ds post hqd]
    exact h.par
  · rw [realPositionSign_mid pre es post hpe, realPositionCharacter_mid pre ds post hpd]
    exact h.sign_p
  · rw [Nat.add_assoc, realPositionSign_mid pre es post hqe,
      realPositionCharacter_mid pre ds post hqd]
    exact h.sign_q
  · intro i d hi hi'
    rcases outside_or_mid (realRank pre) r i with hout | ⟨j, hj, rfl⟩
    · refine ⟨?_, (realInducedBlockAt_of_not_mid hr (by simpa only [he] using hout)).symm.trans hi'⟩
      rcases hout with hl | hl
      · have hh := lt_of_realInducedBlockAt_of_lt hi' hl
        omega
      · omega
    · rw [realInducedBlockAt_mid pre es post (he.symm ▸ hj)] at hi'
      obtain ⟨hdis, hj'⟩ := h.induced_off j d (by omega) hi'
      rw [realInducedBlockAt_mid pre ds post (hd.symm ▸ hj)]
      exact ⟨by omega, hj'⟩
  · intro d hi
    rw [realInducedBlockAt_mid pre es post hpe] at hi
    exact h.induced_p d hi

open InductionStages in
/-- The Frobenius map of the extended data is induction in stages of the
original compact map. -/
def RealBlockFrobeniusInStagesStatement
    (h : IsBlockFrobData r ds es p ε σ μ) (hd : realRank ds = r)
    (hn : realRank (pre ++ es ++ post) = n) : Prop :=
  ∀ (ha : realRank pre + r ≤ n)
    (hk : ∀ k f, blockFrobMap h (kRep r ds k f) = kRep r es k (blockFrobMap h f)),
    blockFrobMap (h.inStages hd hn) = ind ha rfl h.rank hd hn (blockFrobMap h) hk

open InductionStages in
theorem realBlockFrobeniusInStages
    (h : IsBlockFrobData r ds es p ε σ μ) (hd : realRank ds = r)
    (hn : realRank (pre ++ es ++ post) = n) :
    RealBlockFrobeniusInStagesStatement h hd hn := by
  intro ha hk
  ext F : 1
  apply Subtype.ext
  refine eq_of_eqOn_unitaryCompact_of_mem_principalSeries
    (blockFrobMap (h.inStages hd hn) F).2.1.1
    (ind ha rfl h.rank hd hn (blockFrobMap h) hk F).2.1.1 fun κ hκ => ?_
  rw [ind_apply_unitaryCompact ha rfl h.rank hd hn hk F ⟨κ, hκ⟩]
  have hs := RealAmbientCanonicalCharacterBraid.sliceK_frob ha rfl hd h.rank
    h (h.inStages hd hn) ⟨κ, hκ⟩ F
  have he := congrArg (fun v : KF r es => (v : Langlands.GeneralLinear r ℝ → ℂ) 1) hs
  rw [sliceK_apply_one] at he
  exact he

end Langlands.Archimedean.RealBlockFrobeniusMap
