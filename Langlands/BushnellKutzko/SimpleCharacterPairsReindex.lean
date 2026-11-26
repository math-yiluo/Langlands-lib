import Langlands.BushnellKutzko.SimpleCharacterPairs
import Langlands.BushnellKutzko.StratumEquivalenceOrder
import Langlands.BushnellKutzko.StratumEquivalenceCritical

/-! # Simple character pairs at a changed first index -/

open ValuativeRel

noncomputable section

namespace Langlands.BushnellKutzko

universe uF uV

variable {F : Type uF} [Field F] [ValuativeRel F] {V : Type uV} [AddCommGroup V] [Module F V]

local notation "A" => Module.End F V

/-- `k₀(β) < −r` makes the critical depth of `β` exceed `r`. -/
theorem simpleCriticalDepth_gt_of_criticalExponent_lt {L : LatticeChain 𝒪[F] F V} {β : A} {r : ℤ}
    (h : criticalExponent L β < ((-r : ℤ) : WithBot ℤ)) :
    (r : WithTop ℤ) < simpleCriticalDepth L β := by
  unfold simpleCriticalDepth
  cases hk : criticalExponent L β with
  | bot => exact WithTop.coe_lt_top r
  | coe k =>
    rw [hk] at h
    have h' := WithBot.coe_lt_coe.mp h
    exact WithTop.coe_lt_coe.mpr (by omega)

/-- A critical exponent below `−m` and different from `−(m+1)` is below `−(m+1)`. -/
theorem criticalExponent_lt_succ_of_ne {L : LatticeChain 𝒪[F] F V} {β : A} {m : ℕ}
    (h : criticalExponent L β < ((-(m : ℤ) : ℤ) : WithBot ℤ))
    (hne : criticalExponent L β ≠ ((-((m : ℤ) + 1) : ℤ) : WithBot ℤ)) :
    criticalExponent L β < ((-((m : ℤ) + 1) : ℤ) : WithBot ℤ) := by
  cases hk : criticalExponent L β with
  | bot => exact WithBot.bot_lt_coe _
  | coe k =>
    rw [hk] at h hne
    have h' := WithBot.coe_lt_coe.mp h
    have hne' : k ≠ -((m : ℤ) + 1) := fun h => hne (by rw [h])
    exact WithBot.coe_lt_coe.mpr (by omega)

variable [TopologicalSpace F] [IsNonarchimedeanLocalField F]

/-- Change the first index of a defining sequence to another simple index for the same element. -/
def Stratum.DefiningSequenceChoice.reindex {S S' : Stratum 𝒪[F] F V} (hc : S'.chain = S.chain)
    (hn : S'.n = S.n) (hb : S'.b = S.b) (hS' : S'.IsSimple) (q : S.DefiningSequenceChoice) :
    S'.DefiningSequenceChoice := by
  classical
  obtain ⟨hPure, hterms, heq, hr₀, hmono, hstep, hlast, hder⟩ := q.isDefiningSequence
  have hrlt : S'.r < (q.terms 0).n := by
    rw [(hterms 0).2.1, ← hn]
    exact S'.r_lt_n
  let t₀ : Stratum 𝒪[F] F V := { q.terms 0 with r := S'.r, r_lt_n := hrlt }
  let terms (i : Fin (q.steps + 1)) := if i = 0 then t₀ else q.terms i
  have hEl (i) : (terms i).b = (q.terms i).b := by
    by_cases hi : i = 0 <;> simp [terms, hi, t₀]
  have hf₀ : terms 0 = t₀ := ite_eq_left rfl
  have hfs (i : Fin q.steps) : terms i.succ = q.terms i.succ := ite_eq_right i.succ_ne_zero
  have hP : (q.terms 0).chain.endFiltration = S'.chain.endFiltration := by
    rw [hc]
    exact StratumEquivalence.endFiltration_eq_of_equivalent heq
  have hb₀ : (q.terms 0).b = S'.b := q.firstElement.trans hb.symm
  refine ⟨q.steps, terms, ⟨hS'.1, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩, (hEl 0).trans hb₀⟩
  · intro i
    by_cases hi : i = 0
    · subst i
      rw [hf₀]
      refine ⟨?_, (hterms 0).2.1.trans hn.symm, (hterms 0).2.2.1, ?_⟩
      · exact (hterms 0).1.trans (by rw [hc])
      · change criticalExponent (q.terms 0).chain (q.terms 0).b < ((-S'.r : ℤ) : WithBot ℤ)
        rw [StratumEquivalence.criticalExponent_congr hP, hb₀]
        exact hS'.2
    · rw [show terms i = q.terms i from ite_eq_right hi]
      exact ⟨(hterms i).1.trans (by rw [hc]), (hterms i).2.1.trans hn.symm, (hterms i).2.2⟩
  · rw [hf₀]
    change {x : A | x - (q.terms 0).b ∈ (q.terms 0).chain.endFiltration (-S'.r)} =
      {x : A | x - S'.b ∈ S'.chain.endFiltration (-S'.r)}
    rw [hP, hb₀]
  · rw [hf₀]
  · intro i j hij
    have hj : j ≠ 0 := fun h => (not_lt_of_ge (Fin.zero_le i)) (h ▸ hij)
    change (terms i).r < (terms j).r
    rw [show terms j = q.terms j from ite_eq_right hj]
    by_cases hi : i = 0
    · rw [hi, hf₀]
      change S'.r < (q.terms j).r
      have hsteps : 0 < q.steps := by
        have := j.isLt
        have : (j : ℕ) ≠ 0 := fun h => hj (Fin.ext h)
        omega
      let k₀ : Fin q.steps := ⟨0, hsteps⟩
      have hk := (hstep k₀).1
      have hcast : k₀.castSucc = 0 := Fin.ext rfl
      rw [hcast, q.firstElement, ← hb, ← hc] at hk
      have hsimple := hS'.2
      rw [hk] at hsimple
      have h1 : S'.r < (q.terms k₀.succ).r := by
        have := WithBot.coe_lt_coe.mp hsimple
        omega
      have hle : k₀.succ ≤ j := by
        rw [Fin.le_def]
        simp only [k₀, Fin.succ_mk, Fin.val_mk]
        have : (j : ℕ) ≠ 0 := fun h => hj (Fin.ext h)
        omega
      exact h1.trans_le (hmono.monotone hle)
    · rw [show terms i = q.terms i from ite_eq_right hi]
      exact hmono hij
  · intro i
    rw [hfs i, hEl i.castSucc, hc]
    exact hstep i
  · rw [hEl (Fin.last q.steps), hc, hn]
    exact hlast
  · intro i
    rw [hfs i, hEl i.castSucc]
    exact hder i

@[simp] theorem Stratum.DefiningSequenceChoice.reindex_tail {S S' : Stratum 𝒪[F] F V}
    (hc : S'.chain = S.chain) (hn : S'.n = S.n) (hb : S'.b = S.b) (hS' : S'.IsSimple)
    (q : S.DefiningSequenceChoice) :
    (Stratum.DefiningSequenceChoice.reindex hc hn hb hS' q).tail = q.tail := by
  simp [Stratum.DefiningSequenceChoice.reindex, Stratum.DefiningSequenceChoice.tail,
    Fin.succ_ne_zero]

/-- The pairs of a simple stratum do not depend on its simple first index. -/
theorem simpleCharacterPairs_congr (ψF : AddChar F ℂ) {S S' : Stratum 𝒪[F] F V}
    (hc : S'.chain = S.chain) (hn : S'.n = S.n) (hb : S'.b = S.b) (hS : S.IsSimple)
    (hS' : S'.IsSimple) (m : ℕ) :
    simpleCharacterPairs ψF S' m = simpleCharacterPairs ψF S m := by
  have key : ∀ {S S' : Stratum 𝒪[F] F V} (hc : S'.chain = S.chain) (hn : S'.n = S.n)
      (hb : S'.b = S.b) (hS' : S'.IsSimple),
      simpleCharacterPairs ψF S m ⊆ simpleCharacterPairs ψF S' m := by
    intro S S' hc hn hb hS' P hP
    simp only [simpleCharacterPairs, Set.mem_iUnion, Set.mem_image] at hP ⊢
    obtain ⟨q, θ, hθ, rfl⟩ := hP
    refine ⟨Stratum.DefiningSequenceChoice.reindex hc hn hb hS' q, ?_⟩
    rw [Stratum.DefiningSequenceChoice.reindex_tail, hc, hn, hb]
    exact ⟨θ, hθ, rfl⟩
  exact le_antisymm (key hc.symm hn.symm hb.symm hS) (key hc hn hb hS')

end Langlands.BushnellKutzko
