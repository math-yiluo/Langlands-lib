import Langlands.BushnellKutzko.SimpleStratumLatticeInduction
import Langlands.BushnellKutzko.SimpleStratumGroupPropertiesProof
import Langlands.BushnellKutzko.SimpleCharacterCore
import Langlands.BushnellKutzko.SimpleCharacterRestrictionHigh

/-! # High groups along a defining sequence -/

noncomputable section

open ValuativeRel

namespace Langlands.BushnellKutzko

universe uF uV

variable {F : Type uF} [Field F] [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F]
  {V : Type uV} [AddCommGroup V] [Module F V]

local notation "O" => 𝒪[F]
local notation "A" => Module.End F V
local notation "H[" S "," q "]" => simpleHGroup (Stratum.chain S) (Stratum.n S) (Stratum.b S)
  (Stratum.DefiningSequenceChoice.tail q)
local notation "J[" S "," q "]" => simpleJGroup (Stratum.chain S) (Stratum.n S) (Stratum.b S)
  (Stratum.DefiningSequenceChoice.tail q)

omit [TopologicalSpace F] [IsNonarchimedeanLocalField F] in
/-- A simple stratum of depth zero with nonscalar parameter has positive
finite critical depth bounded by the stratum level. -/
theorem criticalDepth_of_simple (S : Stratum O F V) (hS0 : S.r = 0) (hS : S.IsSimple)
    (q : S.DefiningSequenceChoice) (hb : elementAlgebra S.b ≠ ⊥) :
    ∃ r : ℕ, 0 < r ∧ r ≤ S.n ∧
      criticalExponent S.chain S.b = ((-(r : ℤ) : ℤ) : WithBot ℤ) := by
  have hlt := hS.2
  rw [hS0, neg_zero] at hlt
  let k := sSup (criticalIndexSet S.chain S.b)
  have hc : criticalExponent S.chain S.b = (k : WithBot ℤ) := by
    rw [criticalExponent, ite_eq_right hb]
  have hk : k < 0 := by rwa [hc, WithBot.coe_lt_coe] at hlt
  let r := (-k).toNat
  have hr : (r : ℤ) = -k := Int.toNat_of_nonneg (by omega)
  have hcr : criticalExponent S.chain S.b = ((-(r : ℤ) : ℤ) : WithBot ℤ) := by
    rw [hc, hr, neg_neg]
  have hd := q.finiteCriticalDepth_le S.b List.mem_cons_self
  rw [finiteCriticalDepth_of_criticalExponent_eq _ _ _ _ hcr] at hd
  exact ⟨r, by omega, hd, hcr⟩

omit [TopologicalSpace F] [IsNonarchimedeanLocalField F] in
/-- At a terminal term with finite critical exponent, the critical depth is the level. -/
theorem level_eq_of_terminal_of_criticalExponent_eq {S : Stratum O F V}
    (q : S.DefiningSequenceChoice) (hq : q.steps = 0) {r : ℕ}
    (hr : criticalExponent S.chain S.b = ((-(r : ℤ) : ℤ) : WithBot ℤ)) : S.n = r := by
  have htail : q.tail = [] := List.length_eq_zero_iff.mp (by
    simpa only [Stratum.DefiningSequenceChoice.tail, List.length_ofFn] using hq)
  exact (q.finiteCriticalDepth_of_tail_nil htail).symm.trans
    (finiteCriticalDepth_of_criticalExponent_eq S.chain S.n r S.b hr)

/-- The normalized suffix and the high group equalities at a nonterminal step. -/
theorem exists_simpleCharacterSuffix
    (S : Stratum O F V) (hS0 : S.r = 0) (hS : S.IsSimple) (q : S.DefiningSequenceChoice)
    (hq : 0 < q.steps) :
    ∃ (T : Stratum O F V) (q' : T.DefiningSequenceChoice) (r : ℕ),
      T.chain = S.chain ∧ T.n = S.n ∧ T.r = 0 ∧ T.IsSimple ∧
      (r : ℤ) < S.n ∧ criticalExponent S.chain S.b = ((-(r : ℤ) : ℤ) : WithBot ℤ) ∧
      criticalExponent S.chain T.b < ((-(r : ℤ) : ℤ) : WithBot ℤ) ∧
      S.b - T.b ∈ S.chain.endFiltration (-(r : ℤ)) ∧ q.tail = T.b :: q'.tail ∧ q'.steps < q.steps ∧
      (∀ m : ℕ, r / 2 ≤ m → H[S,q] (m + 1) = simpleHGroup S.chain S.n T.b q'.tail (m + 1)) ∧
      (∀ l : ℕ, (r + 1) / 2 ≤ l → J[S,q] l = simpleJGroup S.chain S.n T.b q'.tail l) := by
  let i : Fin q.steps := ⟨0, hq⟩
  let U := q.terms i.succ
  obtain ⟨_, hall, _, hfirst, hmono, hstep, _, _⟩ := q.isDefiningSequence
  have hi : i.castSucc = 0 := Fin.ext rfl
  have hpos : 0 < U.r := by
    have h := hmono (Fin.castSucc_lt_succ (i := i))
    change (q.terms i.castSucc).r < U.r at h
    rwa [hi, hfirst, hS0] at h
  obtain ⟨hOrder, hLevel, hSimple⟩ := hall i.succ
  let U' := U.withChainAndLevel S.chain S.n hOrder.symm hLevel.symm
  let q₀ := (q.suffix i.succ).withChainAndLevel S.chain S.n hOrder.symm hLevel.symm
  let T := U'.atDepthZero (lt_trans (show 0 < U'.r from hpos) U'.r_lt_n)
  let q' : T.DefiningSequenceChoice := q₀.atDepthZero hpos.le
  have hT : T.IsSimple :=
    Stratum.isSimple_atDepthZero (U.isSimple_withChainAndLevel _ _ hOrder.symm hLevel.symm hSimple) hpos.le
  let r := U.r.toNat
  have hr : (r : ℤ) = U.r := Int.toNat_of_nonneg hpos.le
  have hrn : (r : ℤ) < S.n := by rw [hr]; exact U'.r_lt_n
  have h₀ := hstep i
  rw [hi, q.firstElement] at h₀
  have hcrit : criticalExponent S.chain S.b = ((-(r : ℤ) : ℤ) : WithBot ℤ) := by
    rw [hr]
    exact h₀.1
  have hTc : criticalExponent S.chain T.b < ((-(r : ℤ) : ℤ) : WithBot ℤ) := by
    change criticalExponent S.chain U.b < ((-(r : ℤ) : ℤ) : WithBot ℤ)
    rw [hr, LatticeChain.criticalExponent_eq_of_order_eq hOrder.symm]
    exact hSimple.2
  have hδ : S.b - T.b ∈ S.chain.endFiltration (-(r : ℤ)) := by
    rw [hr]
    change S.b - (q.terms i.succ).b ∈ S.chain.endFiltration (-(q.terms i.succ).r)
    simpa only [neg_sub] using neg_mem h₀.2
  have htail : q.tail = T.b :: q'.tail := by
    change q.tail = U.b :: (q.suffix i.succ).tail
    rw [q.tail_suffix]
    have hlen : 0 < q.tail.length := by
      simpa only [Stratum.DefiningSequenceChoice.tail, List.length_ofFn] using hq
    simpa only [U, i, Fin.val_succ, zero_add, List.drop_zero,
      Stratum.DefiningSequenceChoice.tail, List.getElem_ofFn] using
      (List.drop_eq_getElem_cons hlen)
  have hsteps : q'.steps < q.steps := by
    change q.steps - 1 < q.steps
    omega
  have hseq := SimpleStratumLattice.sequence_of_choice S.chain q rfl (by simpa [hS0] using hS.2)
  rw [htail] at hseq
  have hn : 0 < S.n := by omega
  refine ⟨T, q', r, rfl, rfl, rfl, hT, hrn, hcrit, hTc, hδ, htail, hsteps, ?_, ?_⟩
  · intro m hm
    have hcut : SimpleStratumLattice.cutoff .H (r : ℤ) ≤ (m + 1 : ℕ) := by
      change (r : ℤ) / 2 + 1 ≤ _
      omega
    have heq := hseq.high_eq hn hcrit .H hcut
    change simpleHLayer S.chain S.n S.b (T.b :: q'.tail) (m + 1) =
      simpleHLayer S.chain S.n T.b q'.tail (m + 1) at heq
    rw [← htail] at heq
    ext g
    rw [simpleHGroup_mem_iff_of_pos S hS0 hS q (by omega), heq]
    exact (simpleHGroup_mem_iff_of_pos T rfl hT q' (by omega)).symm
  · intro l hl
    have hcut : SimpleStratumLattice.cutoff .J (r : ℤ) ≤ (l : ℤ) := by
      change ((r : ℤ) + 1) / 2 ≤ _
      omega
    have heq := hseq.high_eq hn hcrit .J hcut
    change simpleJLayer S.chain S.n S.b (T.b :: q'.tail) l =
      simpleJLayer S.chain S.n T.b q'.tail l at heq
    rw [← htail] at heq
    ext g
    rw [simpleJGroup_mem_iff_of_pos S hS0 hS q (by omega), heq]
    exact (simpleJGroup_mem_iff_of_pos T rfl hT q' (by omega)).symm

end Langlands.BushnellKutzko
