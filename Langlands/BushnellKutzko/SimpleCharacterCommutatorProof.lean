import Langlands.BushnellKutzko.SimpleCharacterCommutatorInduction
import Langlands.BushnellKutzko.SimpleCharacterForwardRestriction
import Langlands.BushnellKutzko.SimpleStratumLatticePropertiesProof
import Langlands.BushnellKutzko.StratumEquivalenceOrder

/-! # Induction along a defining sequence for the two character commutator formulas -/

noncomputable section

open ValuativeRel
open scoped Pointwise Classical

namespace Langlands.BushnellKutzko

universe uF uV

variable {F : Type uF} [Field F] [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F]
  {V : Type uV} [AddCommGroup V] [Module F V]

local notation "O" => 𝒪[F]
local notation "A" => Module.End F V
local notation "G" => (Module.End F V)ˣ
local notation "H[" S "," q "]" => simpleHGroup (Stratum.chain S) (Stratum.n S) (Stratum.b S)
  (Stratum.DefiningSequenceChoice.tail q)
local notation "J[" S "," q "]" => simpleJGroup (Stratum.chain S) (Stratum.n S) (Stratum.b S)
  (Stratum.DefiningSequenceChoice.tail q)
local notation "C[" ψ "," S "," q "]" => simpleCharacters ψ (Stratum.chain S) (Stratum.n S) (Stratum.b S)
  (Stratum.DefiningSequenceChoice.tail q)

omit [TopologicalSpace F] [IsNonarchimedeanLocalField F] in
private theorem tail_nil_of_criticalExponent_bot (S : Stratum O F V) (q : S.DefiningSequenceChoice)
    (h : criticalExponent S.chain S.b = ⊥) : q.tail = [] := by
  apply List.eq_nil_iff_length_eq_zero.mpr
  rw [Stratum.DefiningSequenceChoice.tail, List.length_ofFn]
  by_contra hq
  let i : Fin q.steps := ⟨0, Nat.pos_of_ne_zero hq⟩
  have hi : i.castSucc = 0 := Fin.ext rfl
  have he := (q.isDefiningSequence.2.2.2.2.2.1 i).1
  rw [hi, q.firstElement, h] at he
  exact WithBot.bot_ne_coe he

omit [TopologicalSpace F] [IsNonarchimedeanLocalField F] in
private theorem elementAlgebra_bot_of_criticalExponent_bot (L : LatticeChain O F V) (b : A)
    (h : criticalExponent L b = ⊥) : elementAlgebra b = ⊥ := by
  by_contra hb
  rw [criticalExponent, ite_eq_right hb] at h
  exact WithBot.coe_ne_bot h

private theorem exists_relative_mul_deepJ
    (S : Stratum O F V) (hS0 : S.r = 0) (hS : S.IsSimple) (q : S.DefiningSequenceChoice)
    {r l : ℕ} (hr : criticalExponent S.chain S.b = ((-(r : ℤ) : ℤ) : WithBot ℤ))
    {y : G} (hy : y ∈ J[S,q] l) :
    ∃ u ∈ relativeUnitFiltration S.chain S.b l, ∃ v ∈ J[S,q] (max l ((r + 1) / 2)), u * v = y := by
  let d := (r + 1) / 2
  by_cases hl : l ≤ d
  · have hb : elementAlgebra S.b ≠ ⊥ := by
      intro h
      rw [criticalExponent, ite_eq_left h] at hr
      exact WithBot.bot_ne_coe hr
    have he : simpleJCutoff (finiteCriticalDepth S.chain S.n S.b) = (d : ℤ) := by
      rw [finiteCriticalDepth_of_criticalExponent_eq S.chain S.n (r : ℤ) S.b hr]
      unfold simpleJCutoff d
      omega
    have hld : (l : ℤ) ≤ simpleJCutoff (finiteCriticalDepth S.chain S.n S.b) := by
      rw [he]
      exact_mod_cast hl
    have h := (simpleStratumGroupProperties F V S hS0 hS q).2.1 hb |>.2 l hld
    rw [he, Int.toNat_natCast] at h
    have hy' : y ∈ (J[S,q] l : Set G) := hy
    rw [h] at hy'
    rw [show (r + 1) / 2 = d from rfl, max_eq_right hl]
    exact hy'
  · rw [show (r + 1) / 2 = d from rfl, max_eq_left (by omega : d ≤ l)]
    exact ⟨1, one_mem _, y, hy, one_mul y⟩

private theorem mixed_eq_of_critical_approximation (L : LatticeChain O F V) (n : ℤ) (b c : A) (r s : ℕ)
    (hc : ∃ T : Stratum O F V, T.chain = L ∧ T.n = n ∧ T.b = c ∧ T.IsSimple)
    (hδ : b - c ∈ L.endFiltration (-(r : ℤ)))
    (hcrit : criticalExponent L c = ((-(s : ℤ) : ℤ) : WithBot ℤ)) (hrs : r < s) (k : ℕ) :
    mixedAdjointLattice L b k (-(r : ℤ)) = centralizerLattice L c k ⊔
      mixedAdjointLattice L c (k + (s - r) : ℕ) (-(s : ℤ)) := by
  obtain ⟨T, hL, hn, hb, hT⟩ := hc
  have hpar := SimpleStratumLattice.parameter_of_pure L hT.1 (congrArg LatticeChain.order hL)
  rw [hn, hb] at hpar
  rw [SimpleStratumLattice.mixed_eq_of_sub_mem L (show c - b ∈ L.endFiltration (-(r : ℤ)) by
    rw [← neg_sub]; exact neg_mem hδ) le_rfl]
  have h := SimpleStratumLattice.mixed_eq_sup L hpar hcrit (k : ℤ) ((s : ℤ) - r) (by omega)
  simpa only [show -(s : ℤ) + ((s : ℤ) - r) = -(r : ℤ) by omega, Nat.cast_add,
    Nat.cast_sub hrs.le] using h

/-- Both commutator formulas follow by induction on defining-sequence length,
using the lattice transport and the forward restriction at the cutoffs. -/
theorem simpleCharacterCommutatorAt

    (ψF : AddChar F ℂ) (hψ : IsBKAdditiveCharacter ψF)
    (S : Stratum O F V) (hS0 : S.r = 0) (hS : S.IsSimple) (q : S.DefiningSequenceChoice)
    {r m : ℕ} (hr : criticalExponent S.chain S.b = ((-(r : ℤ) : ℤ) : WithBot ℤ))
    (hm : r / 2 ≤ m) (hmr : m < r) {θ : H[S,q] (m + 1) →* ℂˣ} (hθ : θ ∈ C[ψF,S,q] m) :
    SimpleCharacterCommutatorAt S.chain ψF S.b J[S,q] r m θ := by
  have bounded (d : ℕ) : ∀ (S : Stratum O F V), S.r = 0 → S.IsSimple →
      ∀ (q : S.DefiningSequenceChoice), q.steps < d → ∀ (r m : ℕ),
      criticalExponent S.chain S.b = ((-(r : ℤ) : ℤ) : WithBot ℤ) → r / 2 ≤ m → m < r →
      ∀ θ ∈ C[ψF,S,q] m, SimpleCharacterCommutatorAt S.chain ψF S.b J[S,q] r m θ := by
    induction d with
    | zero =>
      intro S hS0 hS q hq
      omega
    | succ d ih =>
      intro S hS0 hS q hq r m hr hm hmr θ hθ
      by_cases hq0 : q.steps = 0
      · have htail : q.tail = [] := List.eq_nil_iff_length_eq_zero.mpr (by
          rw [Stratum.DefiningSequenceChoice.tail, List.length_ofFn, hq0])
        have hn_eq : S.n = (r : ℤ) := level_eq_of_terminal_of_criticalExponent_eq q hq0 hr
        have hb : S.b ∈ S.chain.endFiltration (-(r : ℤ)) := by
          rw [← hn_eq]
          exact (StratumEquivalence.mem_of_valuation_eq hS.1.2).1
        generalize hnt : S.n = n at θ hθ ⊢
        have hn' : n = (r : ℤ) := hnt.symm.trans hn_eq
        clear hnt
        subst n
        generalize htt : q.tail = tail at θ hθ ⊢
        have ht' : tail = [] := htt.symm.trans htail
        clear htt
        subst tail
        exact simpleCharacterCommutatorAt_nil S.chain ψF hψ S.b hm hb hθ
      · obtain ⟨T, q', s, hL, hN, hT0, hT, _, hs, hcr, hδ, htail, hlt, hH, hJ⟩ :=
          exists_simpleCharacterSuffix S hS0 hS q (Nat.pos_of_ne_zero hq0)
        have hrs : r = s := by
          exact_mod_cast neg_injective (WithBot.coe_injective (hr.symm.trans hs))
        subst s
        have hJb : ∀ {l : ℕ} {y : G}, 1 ≤ l → y ∈ J[S,q] l →
            ∃ u ∈ relativeUnitFiltration S.chain S.b l, ∃ v ∈ J[S,q] (max l ((r + 1) / 2)), u * v = y :=
          fun _ hy => exists_relative_mul_deepJ S hS0 hS q hr hy
        rcases T with ⟨L', n', r', c, hrc, hcval⟩
        change L' = S.chain at hL
        change n' = S.n at hN
        change r' = 0 at hT0
        subst L' n' r'
        let T : Stratum O F V := ⟨S.chain, S.n, 0, c, hrc, hcval⟩
        change criticalExponent S.chain c < ((-(r : ℤ) : ℤ) : WithBot ℤ) at hcr
        generalize ht : q.tail = tail at θ hθ hH hJ hJb ⊢
        have htail' : tail = c :: q'.tail := ht.symm.trans htail
        clear ht
        subst tail
        apply simpleCharacterCommutatorAt_cons S.chain S.n ψF hψ S.b c q'.tail hr hm hmr hδ
          (hH m hm) hJ hJb _ hθ
        generalize hc : criticalExponent S.chain c = cexp at hcr
        cases cexp using WithBot.recBotCoe with
        | bot =>
          exact Or.inl ⟨elementAlgebra_bot_of_criticalExponent_bot S.chain c hc,
            tail_nil_of_criticalExponent_bot T q' hc⟩
        | coe k =>
          have hkr := WithBot.coe_lt_coe.mp hcr
          let s := (-k).toNat
          have hs : (s : ℤ) = -k := Int.toNat_of_nonneg (by omega)
          have hcs : criticalExponent T.chain T.b = ((-(s : ℤ) : ℤ) : WithBot ℤ) := by
            change criticalExponent S.chain c = _
            rw [hc, hs, neg_neg]
          have hrs : r < s := by omega
          refine Or.inr ⟨s, hrs, by rw [hs, neg_neg],
            mixed_eq_of_critical_approximation S.chain S.n S.b c r s ⟨T, rfl, rfl, rfl, hT⟩ hδ hcs hrs,
            (fun _ hy => exists_relative_mul_deepJ T rfl hT q' hcs hy), ?_⟩
          intro θ₀ hθ₀
          have hj : max m (s / 2) < s := by omega
          have hD := q'.finiteCriticalDepth_le T.b List.mem_cons_self
          rw [finiteCriticalDepth_of_criticalExponent_eq _ _ _ _ hcs] at hD
          change (s : ℤ) ≤ S.n at hD
          have hdeepLevel : ((max m (s / 2) : ℕ) : ℤ) < T.n := by
            change ((max m (s / 2) : ℕ) : ℤ) < S.n
            omega
          have hdeep : (((max m (s / 2) : ℕ) : ℤ) : WithTop ℤ) < simpleCriticalDepth T.chain T.b := by
            rw [SimpleStratumLattice.simpleCriticalDepth_eq _ hcs, WithTop.coe_lt_coe]
            exact_mod_cast hj
          have hθ' := simpleCharacters_restrict_forward ψF T rfl hT q' (le_max_left m (s / 2))
            hdeepLevel hdeep hθ₀
          exact ih T rfl hT q' (by omega) s (max m (s / 2)) hcs (le_max_right _ _) hj _ hθ'
  exact bounded (q.steps + 1) S hS0 hS q (by omega) r m hr hm hmr θ hθ

/-- The mixed and J commutator formula of BK93 (3.2.8), using the subgroup properties of the simple stratum. -/
theorem simpleCharacterMixedJCommutator (ψF : AddChar F ℂ) (hψ : IsBKAdditiveCharacter ψF)
    (S : Stratum O F V) (hS0 : S.r = 0) (hS : S.IsSimple) (q : S.DefiningSequenceChoice)
    {r m k l : ℕ} (hcrit : criticalExponent S.chain S.b = ((-(r : ℤ) : ℤ) : WithBot ℤ))
    (hm : r / 2 ≤ m) (hmr : m < r) (hk : 1 ≤ k) (hl : 1 ≤ l)
    (hkl : m + 1 ≤ k + l) (htrace : r + 1 ≤ k + 2 * l)
    {θ : H[S,q] (m + 1) →* ℂˣ} (hθ : θ ∈ C[ψF,S,q] m) {x y : G}
    (hx : (x : A) - 1 ∈ mixedAdjointLattice S.chain S.b k (-(r : ℤ))) (hy : y ∈ J[S,q] l) :
    characterCommutatorFormula ψF S.b θ x y :=
  (simpleCharacterCommutatorAt ψF hψ S hS0 hS q hcrit hm hmr hθ).mixedJ hk hl hkl htrace hx hy


end Langlands.BushnellKutzko
