import Langlands.BushnellKutzko.SimpleCharacterPairsReindex
import Langlands.BushnellKutzko.SimpleCharacterSuffixGroups
import Langlands.BushnellKutzko.SimpleCharacterRestrictionCutoff

/-! # Forward restriction within the critical depth -/

noncomputable section

open ValuativeRel

namespace Langlands.BushnellKutzko

universe uF uV

variable {F : Type uF} [Field F] [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F]
  {V : Type uV} [AddCommGroup V] [Module F V]

local notation "O" => 𝒪[F]
local notation "A" => Module.End F V
local notation "G" => Aˣ
local notation "H[" S "," q "]" => simpleHGroup (Stratum.chain S) (Stratum.n S) (Stratum.b S)
  (Stratum.DefiningSequenceChoice.tail q)
local notation "C[" ψ "," S "," q "]" => simpleCharacters ψ (Stratum.chain S) (Stratum.n S) (Stratum.b S)
  (Stratum.DefiningSequenceChoice.tail q)

/-- Restriction in the forward direction preserves simplicity at every larger
index within the level and critical bounds. The recursive twist is restricted
along the same defining sequence. -/
theorem simpleCharacters_restrict_forward
    (ψF : AddChar F ℂ) (S : Stratum O F V) (hS0 : S.r = 0) (hS : S.IsSimple)
    (q : S.DefiningSequenceChoice) {m j : ℕ} (hmj : m ≤ j) (hjn : (j : ℤ) < S.n)
    (hjc : ((j : ℤ) : WithTop ℤ) < simpleCriticalDepth S.chain S.b)
    {θ : H[S,q] (m + 1) →* ℂˣ} (hθ : θ ∈ C[ψF,S,q] m) :
    θ.comp (Subgroup.inclusion (simpleHGroup_antitone S.chain S.n S.b q.tail (Nat.succ_le_succ hmj))) ∈
      C[ψF,S,q] j := by
  have bounded (d : ℕ) : ∀ (S : Stratum O F V), S.r = 0 → S.IsSimple → ∀ (q : S.DefiningSequenceChoice),
      q.steps < d → ∀ {m j : ℕ} (hmj : m ≤ j), (j : ℤ) < S.n →
      ((j : ℤ) : WithTop ℤ) < simpleCriticalDepth S.chain S.b →
      ∀ θ ∈ C[ψF,S,q] m,
        θ.comp (Subgroup.inclusion (simpleHGroup_antitone S.chain S.n S.b q.tail (Nat.succ_le_succ hmj))) ∈
          C[ψF,S,q] j := by
    induction d with
    | zero =>
      intro S hS0 hS q hq
      omega
    | succ d ih =>
      intro S hS0 hS q hq m j hmj hjn hjc θ hθ
      by_cases hq0 : q.steps = 0
      · have ht : q.tail = [] := List.eq_nil_iff_length_eq_zero.mpr (by
          rw [Stratum.DefiningSequenceChoice.tail, List.length_ofFn, hq0])
        generalize hu : q.tail = tail at θ hθ ⊢
        have he : tail = [] := hu.symm.trans ht
        clear hu
        subst tail
        exact simpleCharacters_restrict_nil S.chain ψF S.n S.b hmj hθ
      · obtain ⟨T, q', r, hL, hn, hT0, hT, _, hcrit, hc, _, ht, hsteps, hH, _⟩ :=
          exists_simpleCharacterSuffix S hS0 hS q (Nat.pos_of_ne_zero hq0)
        have hjr : j < r := by
          rw [SimpleStratumLattice.simpleCriticalDepth_eq _ hcrit, WithTop.coe_lt_coe] at hjc
          exact_mod_cast hjc
        have hmfd : (m : ℤ) < finiteCriticalDepth S.chain S.n S.b := by
          rw [finiteCriticalDepth_of_criticalExponent_eq _ _ _ _ hcrit]
          omega
        have hjfd : (j : ℤ) < finiteCriticalDepth S.chain S.n S.b := by
          rw [finiteCriticalDepth_of_criticalExponent_eq _ _ _ _ hcrit]
          exact_mod_cast hjr
        have hfhalf : (finiteCriticalDepth S.chain S.n S.b / 2).toNat = r / 2 := by
          rw [finiteCriticalDepth_of_criticalExponent_eq _ _ _ _ hcrit]
          omega
        have hgJ := ((simpleStratumGroupProperties F V S hS0 hS q).2.2.1 (j + 1)).1
        rcases T with ⟨L', n', t', b, hlt', hval'⟩
        change L' = S.chain at hL
        change n' = S.n at hn
        change t' = 0 at hT0
        subst L' n' t'
        let T : Stratum O F V := ⟨S.chain, S.n, 0, b, hlt', hval'⟩
        generalize hu : q.tail = tail at θ hθ hH hgJ ⊢
        have he : tail = b :: q'.tail := hu.symm.trans ht
        clear hu
        subst tail
        simp only [simpleCharacters, ite_eq_left hmfd, ite_eq_left hjfd, Set.mem_ofPred_eq] at hθ ⊢
        rw [hfhalf] at hθ ⊢
        obtain ⟨hdet, hnorm, θ₀, hθ₀, hagree⟩ := hθ
        let i := max m (r / 2)
        let k := max j (r / 2)
        have hik : i ≤ k := max_le_max_right _ hmj
        have hk : k < r := by dsimp [k]; omega
        have hkn : (k : ℤ) < T.n := by change (k : ℤ) < S.n; omega
        have hkc : ((k : ℤ) : WithTop ℤ) < simpleCriticalDepth T.chain T.b := by
          apply simpleCriticalDepth_gt_of_criticalExponent_lt
          exact hc.trans_le (WithBot.coe_le_coe.mpr (by omega))
        let θ₀' := θ₀.comp (Subgroup.inclusion
          (simpleHGroup_antitone S.chain S.n b q'.tail (Nat.succ_le_succ hik)))
        have hθ₀' : θ₀' ∈ C[ψF,T,q'] k := ih T rfl hT q' (by omega) hik hkn hkc θ₀ hθ₀
        let inc := simpleHGroup_antitone S.chain S.n S.b (b :: q'.tail) (Nat.succ_le_succ hmj)
        refine ⟨factorsThroughCentralizerDet_restrict inc hdet, ?_, θ₀', hθ₀', ?_⟩
        · intro g hg
          refine ⟨hgJ hg, ?_⟩
          intro x hx
          exact (hnorm hg).2 (Subgroup.inclusion inc x) (inc hx)
        · intro g
          let hinc := simpleHGroup_antitone S.chain S.n S.b (b :: q'.tail) (Nat.succ_le_succ hik)
          obtain ⟨_, _, hv⟩ := hagree (Subgroup.inclusion hinc g)
          have hgj := simpleHGroup_antitone S.chain S.n S.b (b :: q'.tail)
            (Nat.succ_le_succ (le_max_left j (r / 2))) g.prop
          exact ⟨hgj, (hH k (le_max_right _ _)).le g.prop, hv⟩
  exact bounded (q.steps + 1) S hS0 hS q (by omega) hmj hjn hjc θ hθ

end Langlands.BushnellKutzko
