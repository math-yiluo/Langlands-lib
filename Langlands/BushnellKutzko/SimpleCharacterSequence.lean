import Langlands.BushnellKutzko.SimpleStratumLattices
import Langlands.BushnellKutzko.StratumEquivalenceOrder

/-! # Reindexing defining sequences for simple characters -/

open ValuativeRel

namespace Langlands.BushnellKutzko

universe uF uV

variable {F : Type uF} [Field F] [ValuativeRel F] [TopologicalSpace F]
  [IsNonarchimedeanLocalField F] {V : Type uV} [AddCommGroup V] [Module F V]

namespace LatticeChain

/-- The hereditary order determines every step of the lattice filtration. -/
theorem endFiltration_eq_of_order_eq {L M : LatticeChain 𝒪[F] F V} (h : L.order = M.order) :
    L.endFiltration = M.endFiltration :=
  StratumEquivalence.endFiltration_eq_of_eq
    ((L.toSubmodule_order.symm.trans (congrArg Subalgebra.toSubmodule h)).trans M.toSubmodule_order)

/-- The hereditary order determines the unit filtration. -/
theorem unitFiltration_eq_of_order_eq {L M : LatticeChain 𝒪[F] F V} (h : L.order = M.order) :
    L.unitFiltration = M.unitFiltration := by
  funext k
  ext g
  simp only [mem_unitFiltration, h, endFiltration_eq_of_order_eq h]

/-- The critical exponent is invariant under replacing the chain by one with the same order. -/
theorem criticalExponent_eq_of_order_eq {L M : LatticeChain 𝒪[F] F V} (h : L.order = M.order)
    (b : Module.End F V) : criticalExponent L b = criticalExponent M b := by
  unfold criticalExponent criticalIndexSet adjointLattice centralizerLattice
  rw [endFiltration_eq_of_order_eq h]

end LatticeChain

namespace Stratum

omit [TopologicalSpace F] [IsNonarchimedeanLocalField F] in
/-- Replace the stratum index by zero, keeping its element and lattice chain. -/
def atDepthZero (S : Stratum 𝒪[F] F V) (hn : 0 < S.n) : Stratum 𝒪[F] F V :=
  { S with r := 0, r_lt_n := hn }

omit [TopologicalSpace F] [IsNonarchimedeanLocalField F] in
/-- A simple stratum at a nonnegative index is simple at index zero. -/
theorem isSimple_atDepthZero {S : Stratum 𝒪[F] F V} (hS : S.IsSimple) (hr : 0 ≤ S.r) :
    (S.atDepthZero (hr.trans_lt S.r_lt_n)).IsSimple := by
  refine ⟨hS.1, hS.2.trans_le ?_⟩
  rw [WithBot.coe_le_coe]
  exact neg_nonpos.mpr hr

namespace DefiningSequenceChoice

/-- Reindex the initial stratum and the first term at zero. The tail is unchanged. -/
def atDepthZero {S : Stratum 𝒪[F] F V} (q : S.DefiningSequenceChoice) (hr : 0 ≤ S.r) :
    (S.atDepthZero (hr.trans_lt S.r_lt_n)).DefiningSequenceChoice := by
  obtain ⟨hPure, hTerms, _, hFirstDepth, hMono, hStep, hLast, hDerived⟩ := q.isDefiningSequence
  have hNonneg : 0 ≤ (q.terms 0).r := hFirstDepth.symm ▸ hr
  let terms := Fin.cons ((q.terms 0).atDepthZero (hNonneg.trans_lt (q.terms 0).r_lt_n))
    (α := fun _ => Stratum 𝒪[F] F V) (fun j : Fin q.steps => q.terms j.succ)
  have hElement (j : Fin (q.steps + 1)) : (terms j).b = (q.terms j).b := by
    refine Fin.cases ?_ (fun _ => ?_) j <;> rfl
  have hLater (j : Fin (q.steps + 1)) : j ≠ 0 → terms j = q.terms j := by
    refine Fin.cases (fun h => (h rfl).elim) (fun _ _ => rfl) j
  refine ⟨q.steps, terms, ⟨hPure, ?_, ?_, rfl, ?_, ?_, ?_, ?_⟩, q.firstElement⟩
  · refine Fin.cases ?_ (fun j => hTerms j.succ)
    exact ⟨(hTerms 0).1, (hTerms 0).2.1, isSimple_atDepthZero (hTerms 0).2.2 hNonneg⟩
  · unfold Equivalent coset
    simp only [terms, Fin.cons_zero, Stratum.atDepthZero, neg_zero, q.firstElement]
    rw [LatticeChain.endFiltration_eq_of_order_eq (hTerms 0).1]
  · rw [Fin.strictMono_iff_lt_succ]
    intro j
    change (terms j.castSucc).r < (q.terms j.succ).r
    by_cases hj : j.castSucc = 0
    · have hlt := hMono (Fin.castSucc_lt_succ (i := j))
      rw [hj] at hlt ⊢
      exact hNonneg.trans_lt hlt
    · rw [hLater j.castSucc hj]
      exact hMono Fin.castSucc_lt_succ
  · intro j
    rw [hElement j.castSucc, hElement j.succ]
    exact hStep j
  · rw [hElement (Fin.last q.steps)]
    exact hLast
  · intro j
    rw [hElement j.castSucc, hElement j.succ]
    exact hDerived j

@[simp] theorem tail_atDepthZero {S : Stratum 𝒪[F] F V} (q : S.DefiningSequenceChoice)
    (hr : 0 ≤ S.r) : (q.atDepthZero hr).tail = q.tail := rfl

/-- Start a defining sequence at a selected term and retain its subsequent terms. -/
def suffix {S : Stratum 𝒪[F] F V} (q : S.DefiningSequenceChoice) (i : Fin (q.steps + 1)) :
    (q.terms i).DefiningSequenceChoice := by
  obtain ⟨_, hTerms, _, _, hMono, hStep, hLast, hDerived⟩ := q.isDefiningSequence
  let embed : Fin (q.steps - i.val + 1) → Fin (q.steps + 1) :=
    fun j => ⟨i.val + j.val, by have := i.isLt; have := j.isLt; omega⟩
  have hzero : embed 0 = i := Fin.ext (Nat.add_zero _)
  have hfinal : embed (Fin.last (q.steps - i.val)) = Fin.last q.steps := Fin.ext (by
    have := i.isLt
    change i.val + (q.steps - i.val) = q.steps
    omega)
  have hfil := LatticeChain.endFiltration_eq_of_order_eq (hTerms i).1
  refine ⟨q.steps - i.val, q.terms ∘ embed, ⟨(hTerms i).2.2.1, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩, ?_⟩
  · intro j
    exact ⟨(hTerms (embed j)).1.trans (hTerms i).1.symm,
      (hTerms (embed j)).2.1.trans (hTerms i).2.1.symm, (hTerms (embed j)).2.2⟩
  · rw [Function.comp_apply, hzero]
    rfl
  · rw [Function.comp_apply, hzero]
  · intro a b hab
    apply hMono
    exact Fin.lt_def.mpr (Nat.add_lt_add_left (Fin.lt_def.mp hab) i.val)
  · intro j
    let k : Fin q.steps := ⟨i.val + j.val, by have := i.isLt; have := j.isLt; omega⟩
    have hk := hStep k
    change criticalExponent (q.terms i).chain (q.terms k.castSucc).b =
      ((-(q.terms k.succ).r : ℤ) : WithBot ℤ) ∧
      (q.terms k.succ).b - (q.terms k.castSucc).b ∈ (q.terms i).chain.endFiltration (-(q.terms k.succ).r)
    rw [LatticeChain.criticalExponent_eq_of_order_eq (hTerms i).1, hfil]
    exact hk
  · rw [Function.comp_apply, hfinal, LatticeChain.criticalExponent_eq_of_order_eq (hTerms i).1,
      (hTerms i).2.1]
    exact hLast
  · intro j
    let k : Fin q.steps := ⟨i.val + j.val, by have := i.isLt; have := j.isLt; omega⟩
    exact hDerived k
  · rw [Function.comp_apply, hzero]

/-- The suffix tail consists precisely of the elements after the selected term. -/
theorem tail_suffix {S : Stratum 𝒪[F] F V} (q : S.DefiningSequenceChoice)
    (i : Fin (q.steps + 1)) :
    (q.suffix i).tail = q.tail.drop i.val := by
  have hi := i.isLt
  apply List.ext_getElem
  · simp [Stratum.DefiningSequenceChoice.tail, suffix]
  · intro j hj hj'
    simp only [Stratum.DefiningSequenceChoice.tail, suffix, List.getElem_ofFn, List.getElem_drop,
      Function.comp_apply]
    rfl

end DefiningSequenceChoice
end Stratum

end Langlands.BushnellKutzko
