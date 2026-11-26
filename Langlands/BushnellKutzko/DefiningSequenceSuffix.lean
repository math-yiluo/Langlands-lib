import Langlands.BushnellKutzko.SimpleStratumLattices
import Langlands.BushnellKutzko.StratumEquivalenceCritical
import Langlands.BushnellKutzko.NormalizerProof

/-! # Induction along the tail of a defining sequence -/

open ValuativeRel

namespace Langlands.BushnellKutzko

universe uF uV

variable {F : Type uF} [Field F] [ValuativeRel F] [TopologicalSpace F]
  [IsNonarchimedeanLocalField F] {V : Type uV} [AddCommGroup V] [Module F V]

namespace Stratum

variable {S : Stratum 𝒪[F] F V}

/-- The chain of a stratum with the same hereditary order has the same endomorphism
filtration. -/
theorem endFiltration_eq_of_order_eq {T : Stratum 𝒪[F] F V}
    (h : T.chain.order = S.chain.order) : T.chain.endFiltration = S.chain.endFiltration := by
  apply StratumEquivalence.endFiltration_eq_of_eq (a := 0) (c := 0)
  exact congrArg Subalgebra.toSubmodule h

omit [TopologicalSpace F] [IsNonarchimedeanLocalField F] in
/-- At the end of a defining sequence, the critical exponent is `−n` or `−∞`. -/
theorem DefiningSequenceChoice.terminal_critical (q : S.DefiningSequenceChoice)
    (h : q.steps = 0) :
    criticalExponent S.chain S.b = ((-S.n : ℤ) : WithBot ℤ) ∨
      criticalExponent S.chain S.b = ⊥ := by
  have he : Fin.last q.steps = 0 := Fin.ext (by simpa using h)
  simpa only [he, q.firstElement] using q.isDefiningSequence.2.2.2.2.2.2.1

/-- Removing the head of a nonterminal defining sequence gives a zero-depth
simple stratum on the common chain and a defining sequence with one fewer step. -/
theorem DefiningSequenceChoice.exists_suffix (q : S.DefiningSequenceChoice) (hS : S.r = 0)
    (hq : 0 < q.steps) :
    ∃ (T : Stratum 𝒪[F] F V) (q' : T.DefiningSequenceChoice) (r : ℤ),
      T.chain = S.chain ∧ T.n = S.n ∧ T.r = 0 ∧ T.IsSimple ∧
      0 < r ∧ r < S.n ∧ criticalExponent S.chain S.b = ((-r : ℤ) : WithBot ℤ) ∧
      criticalExponent S.chain T.b < ((-r : ℤ) : WithBot ℤ) ∧
      S.b - T.b ∈ S.chain.endFiltration (-r) ∧
      q.tail = T.b :: q'.tail ∧ q'.steps < q.steps := by
  classical
  rcases q with ⟨d | d, terms, hseq, hfirst⟩
  · exact (Nat.lt_irrefl 0 hq).elim
  rcases hseq with ⟨_, hall, _, hfirstDepth, hmono, hstep, hlast, hderived⟩
  let head := terms (0 : Fin (d + 1)).succ
  obtain ⟨hOrd, hLevel, hSimple⟩ := hall (0 : Fin (d + 1)).succ
  change head.chain.order = S.chain.order at hOrd
  change head.n = S.n at hLevel
  change head.IsSimple at hSimple
  have hP := endFiltration_eq_of_order_eq hOrd
  have hpositive : 0 < head.r := by
    rw [← hS, ← hfirstDepth]
    exact hmono (Fin.succ_pos _)
  have hstrict : head.r < S.n := hLevel ▸ head.r_lt_n
  have hn : 0 < S.n := hpositive.trans hstrict
  have hval : S.chain.valuation head.b = -(S.n : WithTop ℤ) := by
    have hv := hSimple.1.2
    simpa only [LatticeChain.valuation, hP, hLevel] using hv
  let T : Stratum 𝒪[F] F V := ⟨S.chain, S.n, 0, head.b, hn, hval.ge⟩
  have hcrit : criticalExponent S.chain T.b < ((-head.r : ℤ) : WithBot ℤ) :=
    StratumEquivalence.criticalExponent_congr hP head.b ▸ hSimple.2
  have hT : T.IsSimple := by
    refine ⟨⟨?_, hval⟩, ?_⟩
    · obtain ⟨hField, hnorm⟩ := hSimple.1.1
      refine ⟨hField, ?_⟩
      let _ := hField.toField
      intro u
      rw [(normalizer F V S.chain).2.1]
      have h := ((normalizer F V head.chain).2.1 _).mp (hnorm u)
      rwa [hOrd] at h
    · change criticalExponent S.chain T.b < ((-0 : ℤ) : WithBot ℤ)
      exact hcrit.trans_le (WithBot.coe_le_coe.mpr (by omega))
  let next : Fin (d + 1) → Stratum 𝒪[F] F V :=
    Fin.cons T (fun i : Fin d => terms i.succ.succ)
  have hb (i : Fin (d + 1)) : (next i).b = (terms i.succ).b := by
    refine Fin.cases ?_ (fun j => ?_) i
    · simp [next, T, head]
    · simp [next]
  have hr (i : Fin (d + 1)) : (next i).r = if i = 0 then 0 else (terms i.succ).r := by
    refine Fin.cases ?_ (fun j => ?_) i <;> simp [next, T]
  have hnterm (i : Fin (d + 1)) :
      (next i).chain.order = T.chain.order ∧ (next i).n = T.n ∧ (next i).IsSimple := by
    refine Fin.cases ?_ (fun j => ?_) i
    · simpa [next] using hT
    · simpa only [next, Fin.cons_succ] using hall j.succ.succ
  have hmono' : StrictMono (fun i => (next i).r) := by
    intro i j hij
    have hj : j ≠ 0 := ne_of_gt ((Fin.zero_le i).trans_lt hij)
    simp only [hr, hj, ite_false]
    split_ifs
    · rw [← hS, ← hfirstDepth]
      exact hmono (Fin.succ_pos _)
    · exact hmono (Fin.succ_lt_succ_iff.mpr hij)
  have hstep' (i : Fin d) :
      criticalExponent T.chain (next i.castSucc).b = ((-(next i.succ).r : ℤ) : WithBot ℤ) ∧
      (next i.succ).b - (next i.castSucc).b ∈ T.chain.endFiltration (-(next i.succ).r) := by
    simpa only [hb, next, Fin.cons_succ, Fin.succ_castSucc] using hstep i.succ
  have hlast' : criticalExponent T.chain (next (Fin.last d)).b = ((-T.n : ℤ) : WithBot ℤ) ∨
      criticalExponent T.chain (next (Fin.last d)).b = ⊥ := by
    simpa only [hb, Fin.succ_last] using hlast
  have hderived' (i : Fin d) :
      (next i.succ).HasSimpleDerivedStratum ((next i.castSucc).b - (next i.succ).b) := by
    simpa only [hb, next, Fin.cons_succ, Fin.succ_castSucc] using hderived i.succ
  let q' : T.DefiningSequenceChoice :=
    { steps := d
      terms := next
      isDefiningSequence := by
        refine ⟨hT.1, hnterm, ?_, ?_, hmono', hstep', hlast', hderived'⟩
        · simp only [next, Fin.cons_zero, Equivalent]
        · simp only [next, Fin.cons_zero]
      firstElement := by simp only [next, Fin.cons_zero] }
  refine ⟨T, q', head.r, rfl, rfl, rfl, hT, hpositive, hstrict, ?_, hcrit, ?_, ?_, by simp [q']⟩
  · have hc := (hstep (0 : Fin (d + 1))).1
    change (terms 0).b = S.b at hfirst
    simpa only [Fin.castSucc_zero, hfirst] using hc
  · have hc := (hstep (0 : Fin (d + 1))).2
    have hd := (S.chain.endFiltration (-head.r)).neg_mem hc
    change (terms 0).b = S.b at hfirst
    simpa only [Fin.castSucc_zero, hfirst, neg_sub] using hd
  · unfold DefiningSequenceChoice.tail
    rw [List.ofFn_succ]
    congr 1

end Stratum

end Langlands.BushnellKutzko
