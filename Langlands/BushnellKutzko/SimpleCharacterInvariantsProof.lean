import Langlands.BushnellKutzko.SimpleCharacterInvariantsStatement
import Langlands.BushnellKutzko.IntertwiningCentralizerComparison
import Langlands.BushnellKutzko.SimpleCharacterIntertwiningProof
import Langlands.BushnellKutzko.SimpleCharacterForwardRestriction

/-! # Invariants from a common simple character (BK93 (3.5.1), printed p. 117) -/

noncomputable section

open ValuativeRel

namespace Langlands.BushnellKutzko

universe uF uV

namespace CentralizerResidue

variable {F : Type uF} [Field F] [ValuativeRel F] [TopologicalSpace F]
  [IsNonarchimedeanLocalField F] {V : Type uV} [AddCommGroup V] [Module F V]

local notation "A" => Module.End F V
local notation "G" => (Module.End F V)ˣ

/-- At a positive index, the group `H^k(β,𝔄)` is the part of a shallower `H^j(β,𝔄)` lying in
`U^k(𝔄)`. -/
theorem simpleHGroup_eq_inf_unitFiltration (S : Stratum 𝒪[F] F V) (hS0 : S.r = 0)
    (hS : S.IsSimple) (q : S.DefiningSequenceChoice) {j k : ℕ} (hj : 1 ≤ j) (hjk : j ≤ k) :
    simpleHGroup S.chain S.n S.b q.tail k =
      simpleHGroup S.chain S.n S.b q.tail j ⊓ S.chain.unitFiltration k := by
  ext g
  rw [Subgroup.mem_inf, simpleHGroup_mem_iff_of_pos S hS0 hS q (hj.trans hjk),
    simpleHGroup_mem_iff_of_pos S hS0 hS q hj]
  constructor
  · intro hg
    refine ⟨⟨hg.1, S.chain.endFiltration_antitone (by exact_mod_cast hjk) hg.2⟩, ?_⟩
    rw [← simpleHGroup_mem_iff_of_pos S hS0 hS q (hj.trans hjk)] at hg
    exact simpleHGroup_le_unitFiltration _ _ _ _ _ hg
  · rintro ⟨hg, hk⟩
    exact ⟨hg.1, hk.2.2⟩

/-- **The critical depths agree.** Under the hypotheses of `sup_eq_of_pair_eq`, with a common
level `n`, the critical depth of `β` is not smaller than that of `β'`. If it were, `θ` and
`θ'` restrict at the first jump `r` of `β` to a common simple character of the simple stratum
`[𝔄,n,r,γ]` and of `[𝔄,n,r,β']`. Then `𝔅_γ + 𝔓 = 𝔅_{β'} + 𝔓 = 𝔅_β + 𝔓`, contradicting
`sup_ne_of_criticalExponent_eq`. -/
theorem not_simpleCriticalDepth_lt (ψF : AddChar F ℂ) (hψ : IsBKAdditiveCharacter ψF)
    {S T : Stratum 𝒪[F] F V} (hS0 : S.r = 0) (hT0 : T.r = 0) (hS : S.IsSimple)
    (hT : T.IsSimple) (hc : T.chain = S.chain) (hn : T.n = S.n) (q : S.DefiningSequenceChoice)
    (q' : T.DefiningSequenceChoice) {m : ℕ} (hmS : (m : ℤ) < S.n)
    (hcS : ((m : ℤ) : WithTop ℤ) < simpleCriticalDepth S.chain S.b)
    (hcT : ((m : ℤ) : WithTop ℤ) < simpleCriticalDepth T.chain T.b)
    {θ : simpleHGroup S.chain S.n S.b q.tail (m + 1) →* ℂˣ}
    (hθ : θ ∈ simpleCharacters ψF S.chain S.n S.b q.tail m)
    {θ' : simpleHGroup T.chain T.n T.b q'.tail (m + 1) →* ℂˣ}
    (hθ' : θ' ∈ simpleCharacters ψF T.chain T.n T.b q'.tail m)
    (hP : (⟨_, θ⟩ : CharacterPair G) = ⟨_, θ'⟩) :
    ¬ simpleCriticalDepth S.chain S.b < simpleCriticalDepth S.chain T.b := by
  intro hlt
  have := S.chain.finiteDimensional
  have hmT : (m : ℤ) < T.n := hn ▸ hmS
  have hsup := sup_eq_of_pair_eq simpleCharacterIntertwining ψF hψ hS0 hT0 hS hT hc q q' hmS
    hmT hcS hcT hθ hθ' hP
  have hbS : elementAlgebra S.b ≠ ⊥ := by
    intro hb
    have htop : simpleCriticalDepth S.chain S.b = ⊤ := by
      simp [simpleCriticalDepth, criticalExponent, hb]
    rw [htop] at hlt
    exact not_top_lt hlt
  have hbT : elementAlgebra T.b ≠ ⊥ := by
    intro hb
    rw [sup_eq_top_of_elementAlgebra_eq_bot S.chain hb] at hsup
    exact hbS (elementAlgebra_eq_bot_of_sup_eq_top hS.1 hsup)
  have hTdepth := criticalDepth_of_simple T hT0 hT q' hbT
  obtain ⟨R', -, hR'n, hcrit'⟩ := hTdepth
  rw [hc] at hcrit'
  by_cases hq : q.steps = 0
  · obtain ⟨R, -, -, hcrit⟩ := criticalDepth_of_simple S hS0 hS q hbS
    have hSn := level_eq_of_terminal_of_criticalExponent_eq q hq hcrit
    rw [SimpleStratumLattice.simpleCriticalDepth_eq S.chain hcrit,
      SimpleStratumLattice.simpleCriticalDepth_eq S.chain hcrit', WithTop.coe_lt_coe] at hlt
    omega
  obtain ⟨⟨Tc, Tn, Tr, Tb, hTrn, hTv⟩, qγ, R, hTc, hTn, hTr, hTsimple, hRn, hcrit, hTcrit,
    hsub, htail, -, hHsuf, -⟩ := exists_simpleCharacterSuffix S hS0 hS q (Nat.pos_of_ne_zero hq)
  dsimp only at hTc hTn hTr hTcrit hsub htail
  subst hTc hTn hTr
  have hdS : simpleCriticalDepth S.chain S.b = ((R : ℤ) : WithTop ℤ) :=
    SimpleStratumLattice.simpleCriticalDepth_eq S.chain hcrit
  have hmR : m < R := by
    rw [hdS, WithTop.coe_lt_coe] at hcS
    exact_mod_cast hcS
  have hRT : ((R : ℤ) : WithTop ℤ) < simpleCriticalDepth T.chain T.b := by
    rw [hc, ← hdS]
    exact hlt
  have hRγ : ((R : ℤ) : WithTop ℤ) < simpleCriticalDepth S.chain Tb :=
    simpleCriticalDepth_gt_of_criticalExponent_lt hTcrit
  -- The restriction of `θ` at the first jump is a simple character for `γ`.
  have hfwd : ∀ j : ℕ, j ≤ R → ∀ θ₀ ∈ simpleCharacters ψF S.chain S.n Tb qγ.tail j,
      ∀ h : simpleHGroup S.chain S.n Tb qγ.tail (R + 1) ≤
        simpleHGroup S.chain S.n Tb qγ.tail (j + 1),
        θ₀.comp (Subgroup.inclusion h) ∈ simpleCharacters ψF S.chain S.n Tb qγ.tail R :=
    fun j hj θ₀ hθ₀ _ =>
      simpleCharacters_restrict_forward ψF _ rfl hTsimple qγ hj hRn hRγ hθ₀
  have hHjump : simpleHGroup S.chain S.n S.b (Tb :: qγ.tail) (R + 1) =
      simpleHGroup S.chain S.n Tb qγ.tail (R + 1) := by
    have h := hHsuf R (Nat.div_le_self R 2)
    rwa [htail] at h
  have hr : finiteCriticalDepth S.chain S.n S.b = R :=
    finiteCriticalDepth_of_criticalExponent_eq S.chain S.n R S.b hcrit
  have key : ∀ (tl : List A) (χ : simpleHGroup S.chain S.n S.b tl (m + 1) →* ℂˣ),
      χ ∈ simpleCharacters ψF S.chain S.n S.b tl m → tl = Tb :: qγ.tail →
      ∃ χ' ∈ simpleCharacters ψF S.chain S.n Tb qγ.tail R,
        (⟨simpleHGroup S.chain S.n S.b tl (R + 1),
          χ.comp (Subgroup.inclusion
            (simpleHGroup_antitone S.chain S.n S.b tl (by omega)))⟩ : CharacterPair G) =
          ⟨simpleHGroup S.chain S.n Tb qγ.tail (R + 1), χ'⟩ := by
    rintro tl χ hχ rfl
    exact exists_pair_eq_at_jump S.chain ψF hψ S.n hmR hr hsub hHjump hfwd hχ
  obtain ⟨θγ, hθγ, hPγ⟩ := key q.tail θ hθ htail
  -- The restriction of `θ'` at the same index is a simple character for `β'`.
  have hθ'R := simpleCharacters_restrict_forward ψF T hT0 hT q' hmR.le (by omega) hRT hθ'
  -- The two restrictions form the same pair.
  have hHm : simpleHGroup S.chain S.n S.b q.tail (m + 1) =
      simpleHGroup T.chain T.n T.b q'.tail (m + 1) := congrArg Sigma.fst hP
  have hHR : simpleHGroup S.chain S.n S.b q.tail (R + 1) =
      simpleHGroup T.chain T.n T.b q'.tail (R + 1) := by
    rw [simpleHGroup_eq_inf_unitFiltration S hS0 hS q (j := m + 1) (by omega) (by omega),
      simpleHGroup_eq_inf_unitFiltration T hT0 hT q' (j := m + 1) (by omega) (by omega),
      hHm, hc]
  have hPR := pair_restrict_eq hP hHR
    (simpleHGroup_antitone S.chain S.n S.b q.tail (by omega))
    (simpleHGroup_antitone T.chain T.n T.b q'.tail (Nat.succ_le_succ hmR.le))
  -- Compare `𝔅 + 𝔓` at the jump.
  have hsupγ := sup_eq_of_pair_eq simpleCharacterIntertwining ψF hψ
    (S := ⟨S.chain, S.n, 0, Tb, hTrn, hTv⟩) rfl hT0 hTsimple hT hc qγ q' hRn
    (by omega) hRγ hRT hθγ hθ'R (hPγ.symm.trans hPR)
  exact sup_ne_of_criticalExponent_eq (S := S) (T := ⟨S.chain, S.n, 0, Tb, hTrn, hTv⟩) rfl hS.1
    hTsimple.1 hcrit hsub hTcrit (hsupγ.trans hsup.symm)

end CentralizerResidue

open CentralizerResidue in
/-- **BK93 (3.5.1), printed p. 117.** Two simple strata on one lattice chain at the same
levels that share a simple character pair have the same critical exponent, ramification
index and residue degree. -/
theorem simpleCharacterInvariants : SimpleCharacterInvariantsStatement.{uF, uV} := by
  intro F _ _ _ _ V _ _ _ ψF hψ L n m S T
  rcases S with ⟨S, hSc, hSn, hSr, hS⟩
  rcases T with ⟨T, hTc, hTn, hTr, hT⟩
  rintro ⟨P, hPS, hPT⟩
  simp only [simpleCharacterPairs, Set.mem_iUnion, Set.mem_image] at hPS hPT
  obtain ⟨q, θ, hθ, rfl⟩ := hPS
  obtain ⟨q', θ', hθ', hP⟩ := hPT
  dsimp only at hθ hθ' hP ⊢
  subst hSc hSn
  have hc : T.chain = S.chain := hTc
  have hnT : T.n = S.n := hTn
  have hS0 : 0 ≤ S.r := by rw [hSr]; exact Int.natCast_nonneg m
  have hT0 : 0 ≤ T.r := by rw [hTr]; exact Int.natCast_nonneg m
  have hmS : (m : ℤ) < S.n := hSr ▸ S.r_lt_n
  have hmT : (m : ℤ) < T.n := hTr ▸ T.r_lt_n
  have hcS : ((m : ℤ) : WithTop ℤ) < simpleCriticalDepth S.chain S.b :=
    hSr ▸ lt_simpleCriticalDepth_of_isSimple hS
  have hcT : ((m : ℤ) : WithTop ℤ) < simpleCriticalDepth T.chain T.b :=
    hTr ▸ lt_simpleCriticalDepth_of_isSimple hT
  let S₀ := S.atDepthZero (hS0.trans_lt S.r_lt_n)
  let T₀ := T.atDepthZero (hT0.trans_lt T.r_lt_n)
  have hS₀ : S₀.IsSimple := Stratum.isSimple_atDepthZero hS hS0
  have hT₀ : T₀.IsSimple := Stratum.isSimple_atDepthZero hT hT0
  have hsup := sup_eq_of_pair_eq simpleCharacterIntertwining ψF hψ (S := S₀) (T := T₀) rfl rfl
    hS₀ hT₀ hc (q.atDepthZero hS0) (q'.atDepthZero hT0) hmS hmT hcS hcT hθ hθ' hP.symm
  have hlt₁ := not_simpleCriticalDepth_lt ψF hψ (S := S₀) (T := T₀) rfl rfl hS₀ hT₀ hc hnT
    (q.atDepthZero hS0) (q'.atDepthZero hT0) hmS hcS hcT hθ hθ' hP.symm
  have hlt₂ := not_simpleCriticalDepth_lt ψF hψ (S := T₀) (T := S₀) rfl rfl hT₀ hS₀ hc.symm
    hnT.symm (q'.atDepthZero hT0) (q.atDepthZero hS0) hmT hcT hcS hθ' hθ hP
  change ¬ simpleCriticalDepth S.chain S.b < simpleCriticalDepth S.chain T.b at hlt₁
  change ¬ simpleCriticalDepth T.chain T.b < simpleCriticalDepth T.chain S.b at hlt₂
  rw [hc] at hlt₂
  refine ⟨criticalExponent_eq_of_simpleCriticalDepth_eq S.chain
    (le_antisymm (not_lt.mp hlt₂) (not_lt.mp hlt₁)), ?_⟩
  exact invariants_eq_of_sup_eq hc.symm hS.1 hT.1 hsup

end Langlands.BushnellKutzko
