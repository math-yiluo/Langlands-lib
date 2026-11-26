import Langlands.BushnellKutzko.SimpleStratumLattices
import Langlands.BushnellKutzko.StratumApproximationReduction
import Langlands.BushnellKutzko.StratumEquivalenceCritical
import Langlands.BushnellKutzko.MinimalCriticalExponentProof
import Langlands.BushnellKutzko.CriticalDerivedStratumProof

/-! # Defining sequences at changed stratum indices -/

open ValuativeRel

noncomputable section

namespace Langlands.BushnellKutzko.Stratum

universe uF uV

variable {F : Type uF} [Field F] [ValuativeRel F]
  {V : Type uV} [AddCommGroup V] [Module F V]

local notation "A" => Module.End F V

/-- Lowering the stratum index keeps the chain, level and element. -/
def lowerIndex (S : Stratum 𝒪[F] F V) (r : ℤ) (hr : r ≤ S.r) : Stratum 𝒪[F] F V :=
  { S with r := r, r_lt_n := hr.trans_lt S.r_lt_n }

/-- Simplicity persists when the stratum index decreases. -/
theorem IsSimple.lowerIndex {S : Stratum 𝒪[F] F V} (hS : S.IsSimple) {r : ℤ} (hr : r ≤ S.r) :
    (S.lowerIndex r hr).IsSimple :=
  ⟨hS.1, hS.2.trans_le (WithBot.coe_le_coe.mpr (neg_le_neg hr))⟩

variable [TopologicalSpace F] [IsNonarchimedeanLocalField F]

/-- Lower the first index of a defining sequence without changing its elements or later strata. -/
def DefiningSequenceChoice.lowerIndex {S : Stratum 𝒪[F] F V} (q : S.DefiningSequenceChoice)
    {r : ℤ} (hr : r ≤ S.r) : (S.lowerIndex r hr).DefiningSequenceChoice := by
  classical
  obtain ⟨hPure, hterms, heq, hr₀, hmono, hstep, hlast, hder⟩ := q.isDefiningSequence
  let terms (i : Fin (q.steps + 1)) :=
    if i = 0 then (q.terms 0).lowerIndex r (hr.trans_eq hr₀.symm) else q.terms i
  have hEl (i) : (terms i).b = (q.terms i).b := by
    by_cases hi : i = 0 <;> simp [terms, hi, Stratum.lowerIndex]
  have hf₀ : terms 0 = (q.terms 0).lowerIndex r (hr.trans_eq hr₀.symm) := ite_eq_left rfl
  have hfs (i : Fin q.steps) : terms i.succ = q.terms i.succ := ite_eq_right i.succ_ne_zero
  refine ⟨q.steps, terms, ⟨hPure, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩, (hEl 0).trans q.firstElement⟩
  · intro i
    by_cases hi : i = 0
    · subst i
      rw [hf₀]
      exact ⟨(hterms 0).1, (hterms 0).2.1, (hterms 0).2.2.lowerIndex (hr.trans_eq hr₀.symm)⟩
    · rw [show terms i = q.terms i from ite_eq_right hi]
      exact hterms i
  · rw [hf₀]
    have hP := StratumEquivalence.endFiltration_eq_of_equivalent heq
    change {x : A | x - (q.terms 0).b ∈ (q.terms 0).chain.endFiltration (-r)} =
      {x : A | x - S.b ∈ S.chain.endFiltration (-r)}
    rw [hP, q.firstElement]
  · rw [hf₀]
    rfl
  · intro i j hij
    have hj : j ≠ 0 := fun h => (not_lt_of_ge (Fin.zero_le i)) (h ▸ hij)
    change (terms i).r < (terms j).r
    rw [show terms j = q.terms j from ite_eq_right hj]
    by_cases hi : i = 0
    · rw [hi, hf₀]
      exact (hr.trans_eq hr₀.symm).trans_lt (hmono (hi ▸ hij))
    · rw [show terms i = q.terms i from ite_eq_right hi]
      exact hmono hij
  · intro i
    simpa only [hfs i, hEl i.castSucc, Stratum.lowerIndex] using hstep i
  · simpa only [hEl (Fin.last q.steps), Stratum.lowerIndex] using hlast
  · intro i
    simpa only [hfs i, hEl i.castSucc] using hder i

@[simp] theorem DefiningSequenceChoice.lowerIndex_tail {S : Stratum 𝒪[F] F V}
    (q : S.DefiningSequenceChoice) {r : ℤ} (hr : r ≤ S.r) : (q.lowerIndex hr).tail = q.tail := by
  simp [DefiningSequenceChoice.lowerIndex, DefiningSequenceChoice.tail, Fin.succ_ne_zero]

/-- Prepend a simple stratum to an exact defining sequence of its critical approximation. -/
def DefiningSequenceChoice.prepend {S T : Stratum 𝒪[F] F V} (hS : S.IsSimple)
    (hT : S.IsCriticalApproximation T) (q : T.DefiningSequenceChoice) (h₀ : q.terms 0 = T)
    (hDer : T.HasSimpleDerivedStratum (S.b - T.b)) : S.DefiningSequenceChoice := by
  obtain ⟨horder, hn, _, hk, hcongr⟩ := hT
  obtain ⟨_, hterms, _, hr, hmono, hstep, hlast, hder⟩ := q.isDefiningSequence
  have hrt : S.r < T.r := by
    have h := hS.2
    rw [hk] at h
    have h' := WithBot.coe_lt_coe.mp h
    omega
  have hp := StratumEquivalence.endFiltration_eq_of_eq (show T.chain.endFiltration 0 =
      S.chain.endFiltration 0 from congrArg Subalgebra.toSubmodule horder)
  refine ⟨q.steps + 1, Fin.cons S q.terms, ⟨hS.1, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩, rfl⟩
  · refine Fin.cases ?_ (fun i => ?_)
    · rw [Fin.cons_zero]
      exact ⟨rfl, rfl, hS⟩
    · rw [Fin.cons_succ]
      exact ⟨(hterms i).1.trans horder, (hterms i).2.1.trans hn, (hterms i).2.2⟩
  · rw [Fin.cons_zero]
    rfl
  · rw [Fin.cons_zero]
  · rw [Fin.strictMono_iff_lt_succ]
    refine Fin.cases ?_ (fun i => ?_)
    · rw [Fin.castSucc_zero, Fin.cons_zero, Fin.cons_succ, hr]
      exact hrt
    · rw [← Fin.succ_castSucc, Fin.cons_succ, Fin.cons_succ]
      exact hmono Fin.castSucc_lt_succ
  · refine Fin.cases ?_ (fun i => ?_)
    · rw [Fin.castSucc_zero, Fin.cons_zero, Fin.cons_succ, h₀]
      exact ⟨hk, hcongr⟩
    · rw [← Fin.succ_castSucc, Fin.cons_succ, Fin.cons_succ]
      rw [← hp, ← StratumEquivalence.criticalExponent_congr hp]
      exact hstep i
  · rw [← Fin.succ_last, Fin.cons_succ, ← StratumEquivalence.criticalExponent_congr hp, ← hn]
    exact hlast
  · refine Fin.cases ?_ (fun i => ?_)
    · rw [Fin.castSucc_zero, Fin.cons_zero, Fin.cons_succ, h₀]
      exact hDer
    · rw [← Fin.succ_castSucc, Fin.cons_succ, Fin.cons_succ]
      exact hder i

@[simp] theorem DefiningSequenceChoice.prepend_tail {S T : Stratum 𝒪[F] F V} (hS : S.IsSimple)
    (hT : S.IsCriticalApproximation T) (q : T.DefiningSequenceChoice) (h₀ : q.terms 0 = T)
    (hDer : T.HasSimpleDerivedStratum (S.b - T.b)) :
    (q.prepend hS hT h₀ hDer).tail = T.b :: q.tail := by
  simp [DefiningSequenceChoice.prepend, DefiningSequenceChoice.tail, List.ofFn_succ, h₀]

private def terminalChoice (S : Stratum 𝒪[F] F V) (hS : S.IsSimple)
    (h : criticalExponent S.chain S.b = ((-S.n : ℤ) : WithBot ℤ) ∨
      criticalExponent S.chain S.b = ⊥) : S.DefiningSequenceChoice :=
  ⟨0, fun _ => S, ⟨hS.1, fun _ => ⟨rfl, rfl, hS⟩, rfl, rfl,
    (by
      intro i j hij
      rw [Fin.lt_def] at hij
      have hi := i.isLt
      have hj := j.isLt
      omega),
    fun i => i.elim0, h, fun i => i.elim0⟩, rfl⟩

set_option maxHeartbeats 800000 in
/-- A simple stratum has a defining sequence beginning with that exact stratum,
provided pure-stratum approximation on the same chain. -/
theorem exists_exact_definingSequenceChoice (hApprox : PureStratumSimpleApproximationStatement.{uF, uV})
    (S : Stratum 𝒪[F] F V) (hS : S.IsSimple) :
    ∃ q : S.DefiningSequenceChoice, q.terms 0 = S ∧ ∀ i, (q.terms i).chain = S.chain := by
  suffices h : ∀ (d : ℕ) (S : Stratum 𝒪[F] F V), (S.n - S.r).toNat = d → S.IsSimple →
      ∃ q : S.DefiningSequenceChoice, q.terms 0 = S ∧ ∀ i, (q.terms i).chain = S.chain from
    h _ S rfl hS
  intro d
  induction d using Nat.strong_induction_on with
  | _ d ih =>
    intro S hd hS
    by_cases hstop : criticalExponent S.chain S.b = ((-S.n : ℤ) : WithBot ℤ) ∨
        criticalExponent S.chain S.b = ⊥
    · exact ⟨terminalChoice S hS hstop, rfl, fun _ => rfl⟩
    obtain ⟨k, hk⟩ : ∃ k : ℤ, criticalExponent S.chain S.b = (k : WithBot ℤ) := by
      cases h : criticalExponent S.chain S.b with
      | bot => exact (hstop (.inr h)).elim
      | coe k => exact ⟨k, rfl⟩
    let := S.chain.finiteDimensional
    have hlow := neg_n_le_criticalExponent minimalCriticalExponent S hS.1 hk
    have hne : k ≠ -S.n := fun h => hstop (.inl (by rw [hk, h]))
    have hrn : -k < S.n := by omega
    have hr : S.r < -k := by
      have hh := hS.2
      rw [hk] at hh
      have h := WithBot.coe_lt_coe.mp hh
      omega
    let R : Stratum 𝒪[F] F V := { S with r := -k, r_lt_n := hrn }
    obtain ⟨T, hc, hn, ht, hT, hEq, _, _⟩ := hApprox F V R hS.1
    have hc' : T.chain = S.chain := hc
    have hn' : T.n = S.n := hn
    have ht' : T.r = -k := ht
    have hkR : criticalExponent R.chain R.b = ((-R.r : ℤ) : WithBot ℤ) := by
      simpa only [R, neg_neg] using hk
    have hder := criticalDerivedStratum F V R T hS.1 hkR hc hn ht hT hEq
    have hTcrit : S.IsCriticalApproximation T := by
      refine ⟨by rw [hc'], hn', hT, ?_, ?_⟩
      · rw [hk, ht', neg_neg]
      · have h := Stratum.sub_mem_of_equivalent (S := T) (T := R) hEq.symm
        simpa only [R, hc', ht', neg_neg] using h
    have hdec : (T.n - T.r).toNat < d := by
      rw [hn', ht', ← hd]
      omega
    obtain ⟨q, h₀, hqchain⟩ := ih _ hdec T rfl hT
    refine ⟨q.prepend hS hTcrit h₀ hder, rfl, ?_⟩
    refine Fin.cases ?_ (fun i => ?_)
    · rfl
    · exact (hqchain i).trans hc'

omit [TopologicalSpace F] [IsNonarchimedeanLocalField F] in
/-- The stopping criterion forces the tail of every defining sequence to be empty. -/
theorem DefiningSequenceChoice.tail_eq_nil_of_terminal {S : Stratum 𝒪[F] F V}
    (q : S.DefiningSequenceChoice)
    (h : criticalExponent S.chain S.b = ((-S.n : ℤ) : WithBot ℤ) ∨
      criticalExponent S.chain S.b = ⊥) : q.tail = [] := by
  have hzero : q.steps = 0 := by
    by_contra hsteps
    let i : Fin q.steps := ⟨0, Nat.pos_of_ne_zero hsteps⟩
    obtain ⟨_, hall, _, _, _, hstep, _, _⟩ := q.isDefiningSequence
    have hfirst : i.castSucc = 0 := Fin.ext rfl
    have hcrit := (hstep i).1
    rw [hfirst, q.firstElement] at hcrit
    rcases h with hn | hbot
    · have hr := WithBot.coe_injective (hcrit.symm.trans hn)
      have hn' := (hall i.succ).2.1
      have hlt := (q.terms i.succ).r_lt_n
      omega
    · exact WithBot.bot_ne_coe (hbot.symm.trans hcrit)
  exact List.length_eq_zero_iff.mp (by simpa [DefiningSequenceChoice.tail] using hzero)

end Langlands.BushnellKutzko.Stratum
