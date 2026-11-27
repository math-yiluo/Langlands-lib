import Langlands.BushnellKutzko.ClassCoverInduction
import Langlands.BushnellKutzko.SimpleCharacterSequence
import Langlands.BushnellKutzko.SimpleCharacterTransferSequences
import Langlands.BushnellKutzko.DefiningSequenceSuffix
import Langlands.BushnellKutzko.SimpleStratumGroupPropertiesStatement
import Langlands.BushnellKutzko.SimpleCharacterChoiceStatement
import Langlands.BushnellKutzko.SimpleCharacterConjugationStatement
import Langlands.BushnellKutzko.SimpleCharacterCore

/-! # Covering simple-character classes: restriction, transport and nonemptiness -/

open ValuativeRel
open Langlands.Group.RelativeWeyl

noncomputable section

namespace Langlands.BushnellKutzko

universe uF uV

variable {F : Type uF} [Field F] [ValuativeRel F] [TopologicalSpace F]
  [IsNonarchimedeanLocalField F] {V : Type uV} [AddCommGroup V] [Module F V]

local notation "A" => Module.End F V
local notation "G" => (Module.End F V)ˣ

namespace Stratum

/-- Move a defining sequence to a simple stratum with the same order, level and element,
keeping all later terms. -/
def DefiningSequenceChoice.reindexSimple {S : Stratum 𝒪[F] F V} (q : S.DefiningSequenceChoice)
    (S' : Stratum 𝒪[F] F V) (horder : S'.chain.order = S.chain.order) (hn : S'.n = S.n)
    (hb : S'.b = S.b) (hS' : S'.IsSimple) : S'.DefiningSequenceChoice := by
  obtain ⟨hPure, hTerms, _, _, hMono, hStep, hLast, hDerived⟩ := q.isDefiningSequence
  have hfil := LatticeChain.endFiltration_eq_of_order_eq horder
  have hcrit := LatticeChain.criticalExponent_eq_of_order_eq horder
  let terms := Fin.cons S' (α := fun _ => Stratum 𝒪[F] F V) (fun j : Fin q.steps => q.terms j.succ)
  have hElement (j : Fin (q.steps + 1)) : (terms j).b = (q.terms j).b := by
    refine Fin.cases ?_ (fun _ => ?_) j
    · exact hb.trans q.firstElement.symm
    · rfl
  refine ⟨q.steps, terms, ⟨hS'.1, ?_, rfl, rfl, ?_, ?_, ?_, ?_⟩, rfl⟩
  · refine Fin.cases ⟨rfl, rfl, hS'⟩ (fun j => ?_)
    exact ⟨(hTerms j.succ).1.trans horder.symm, (hTerms j.succ).2.1.trans hn.symm,
      (hTerms j.succ).2.2⟩
  · rw [Fin.strictMono_iff_lt_succ]
    intro j
    change (terms j.castSucc).r < (q.terms j.succ).r
    by_cases hj : j.castSucc = 0
    · rw [hj]
      change S'.r < (q.terms j.succ).r
      have h1 := (hStep j).1
      rw [hj, q.firstElement] at h1
      have h2 := hS'.2
      rw [hb, hcrit, h1] at h2
      exact neg_lt_neg_iff.mp (WithBot.coe_lt_coe.mp h2)
    · obtain ⟨i, hi⟩ := Fin.exists_succ_eq.mpr hj
      have hti : terms j.castSucc = q.terms j.castSucc := by
        rw [← hi]
        rfl
      rw [hti]
      exact hMono Fin.castSucc_lt_succ
  · intro j
    rw [hElement j.castSucc, hElement j.succ, hfil, hcrit]
    exact hStep j
  · rw [hElement (Fin.last q.steps), hcrit, hn]
    exact hLast
  · intro j
    rw [hElement j.castSucc, hElement j.succ]
    exact hDerived j

@[simp] theorem DefiningSequenceChoice.tail_reindexSimple {S : Stratum 𝒪[F] F V}
    (q : S.DefiningSequenceChoice) (S' : Stratum 𝒪[F] F V) (horder : S'.chain.order = S.chain.order)
    (hn : S'.n = S.n) (hb : S'.b = S.b) (hS' : S'.IsSimple) :
    (q.reindexSimple S' horder hn hb hS').tail = q.tail := rfl

end Stratum

section Premises

variable (ψF : AddChar F ℂ)

/-- For `ψ_F` trivial on `𝔭_F` and nontrivial on `𝔬_F` and a simple stratum `[𝔄,n,m,β]` with
`m ≥ 0`, `Ĉ(𝔄,m,β)` is nonempty, assuming the approximation and restriction statements. -/
theorem simpleCharacterPairs_nonempty (hApprox : PureStratumSimpleApproximationStatement.{uF, uV})
    (hRestr : SimpleCharacterRestrictionStatement.{uF, uV}) (hψ : IsBKAdditiveCharacter ψF)
    (S : Stratum 𝒪[F] F V) (hS : S.IsSimple) (m : ℕ) (hr : S.r = m) :
    (simpleCharacterPairs ψF S m).Nonempty := by
  obtain ⟨q, -, -⟩ := Stratum.exists_exact_definingSequenceChoice hApprox S hS
  have h0 : (0 : ℤ) ≤ S.r := by omega
  obtain ⟨-, -, -, -, he⟩ := hRestr F V ψF hψ (S.atDepthZero (h0.trans_lt S.r_lt_n)) rfl
    (Stratum.isSimple_atDepthZero hS h0) (q.atDepthZero h0)
  obtain ⟨θ, hθ⟩ := he m (by have := S.r_lt_n; change (m : ℤ) < S.n; omega)
  exact ⟨_, Set.mem_iUnion.mpr ⟨q, θ, hθ, rfl⟩⟩

omit [TopologicalSpace F] [IsNonarchimedeanLocalField F] in
/-- At an index at or above the critical depth of `β`, the simple characters attached to
`β` are those of the next element of the defining sequence. -/
theorem simpleCharacters_cons_of_le_depth (L : LatticeChain 𝒪[F] F V) (n : ℤ) (β γ : A)
    (tail : List A) (k : ℕ) (hk : finiteCriticalDepth L n β ≤ (k : ℤ))
    {θ : simpleHGroup L n β (γ :: tail) (k + 1) →* ℂˣ}
    (hθ : θ ∈ simpleCharacters ψF L n β (γ :: tail) k) :
    ∃ θ₀ ∈ simpleCharacters ψF L n γ tail k,
      (⟨_, θ⟩ : CharacterPair G) = ⟨simpleHGroup L n γ tail (k + 1), θ₀⟩ := by
  have hkr : ¬ (k : ℤ) < finiteCriticalDepth L n β := not_lt.mpr hk
  simp only [simpleCharacters, ite_eq_right hkr] at hθ
  obtain ⟨θ₀, hθ₀, hH, ha⟩ := hθ
  refine ⟨θ₀, hθ₀, CharacterPair.ext_of_eq hH (fun g hP hQ => ?_)⟩
  obtain ⟨h₁, h₂, h⟩ := ha ⟨g, hP⟩
  exact Units.ext (by simpa using h)

/-- Let `k + 1 < n`, let `[𝔄,n,k,β]` be a simple stratum on `L` and fix a defining sequence for
it. A character of the group at index `k + 2` that lies in the set of simple characters at
index `k + 1` computed with this defining sequence is, as a pair, an element of
`Ĉ(𝔄,k+1,γ)` for a simple stratum `[𝔄,n,k+1,γ]` on `L` with `γ ≡ β (mod 𝔓^{-(k+1)})`. Here
`ψ_F` is an arbitrary additive character of `F`. -/
theorem exists_pair_mem_succ (L : LatticeChain 𝒪[F] F V) (n : ℤ) (k : ℕ)
    (hk : (k : ℤ) + 1 < n) (S : Stratum 𝒪[F] F V) (hSL : S.chain = L) (hSn : S.n = n)
    (hSr : S.r = k) (hS : S.IsSimple) (q : S.DefiningSequenceChoice)
    {θ : simpleHGroup S.chain S.n S.b q.tail (k + 2) →* ℂˣ}
    (hθ : θ ∈ simpleCharacters ψF S.chain S.n S.b q.tail (k + 1)) :
    ∃ T : SimpleStratumAt L n ((k + 1 : ℕ) : ℤ),
      T.1.b - S.b ∈ L.endFiltration (-((k + 1 : ℕ) : ℤ)) ∧
      (⟨_, θ⟩ : CharacterPair G) ∈ simpleCharacterPairs ψF T.1 (k + 1) := by
  subst hSL hSn
  by_cases hcrit : criticalExponent S.chain S.b < ((-((k + 1 : ℕ) : ℤ) : ℤ) : WithBot ℤ)
  · let S' : Stratum 𝒪[F] F V :=
      { S with r := ((k + 1 : ℕ) : ℤ), r_lt_n := by push_cast; omega }
    have hS' : S'.IsSimple := ⟨hS.1, hcrit⟩
    exact ⟨⟨S', rfl, rfl, rfl, hS'⟩, by simp [S'],
      Set.mem_iUnion.mpr ⟨q.reindexSimple S' rfl rfl rfl hS', θ, hθ, rfl⟩⟩
  · -- the critical case: `k + 1` is the critical depth of `β`
    have h0 : (0 : ℤ) ≤ S.r := by omega
    have hsteps : 0 < (q.atDepthZero h0).steps := by
      by_contra hzero
      have ht := Stratum.DefiningSequenceChoice.terminal_critical (q.atDepthZero h0) (by omega)
      change criticalExponent S.chain S.b = ((-S.n : ℤ) : WithBot ℤ) ∨
        criticalExponent S.chain S.b = ⊥ at ht
      rcases ht with ht | ht
      · apply hcrit
        rw [ht]
        exact WithBot.coe_lt_coe.mpr (by push_cast; omega)
      · apply hcrit
        rw [ht]
        exact WithBot.bot_lt_coe _
    obtain ⟨T, q'', r, hTchain, hTn, -, hT, hr0, hrn, hcritS, hcritT, hsub, htail, -⟩ :=
      (q.atDepthZero h0).exists_suffix rfl hsteps
    change criticalExponent S.chain S.b = _ at hcritS
    change criticalExponent S.chain T.b < _ at hcritT
    change q.tail = T.b :: q''.tail at htail
    change S.b - T.b ∈ S.chain.endFiltration (-r) at hsub
    have hrk : r = ((k + 1 : ℕ) : ℤ) := by
      have hlt := hS.2
      rw [hcritS] at hlt hcrit
      have h1 := WithBot.coe_lt_coe.mp hlt
      have h2 : ¬ (-r < -((k + 1 : ℕ) : ℤ)) := fun h => hcrit (WithBot.coe_lt_coe.mpr h)
      push_cast at h1 h2 ⊢
      omega
    subst hrk
    let T' : Stratum 𝒪[F] F V :=
      { T.withChainAndLevel S.chain S.n (by rw [hTchain]; rfl) hTn.symm with
        r := ((k + 1 : ℕ) : ℤ), r_lt_n := hrn }
    have hT' : T'.IsSimple :=
      ⟨(Stratum.isSimple_withChainAndLevel T S.chain S.n (by rw [hTchain]; rfl) hTn.symm hT).1,
        hcritT⟩
    have key : ∀ (l : List A), l = T.b :: q''.tail →
        ∀ θ : simpleHGroup S.chain S.n S.b l (k + 2) →* ℂˣ,
        θ ∈ simpleCharacters ψF S.chain S.n S.b l (k + 1) →
        (⟨_, θ⟩ : CharacterPair G) ∈ simpleCharacterPairs ψF T' (k + 1) := by
      rintro l rfl θ hθ
      obtain ⟨θ₀, hθ₀, heq⟩ := simpleCharacters_cons_of_le_depth ψF S.chain S.n S.b T.b
        q''.tail (k + 1) (by rw [finiteCriticalDepth_of_criticalExponent_eq S.chain S.n _ S.b hcritS])
        hθ
      rw [heq]
      exact Set.mem_iUnion.mpr
        ⟨q''.reindexSimple T' (by rw [hTchain]; rfl) hTn.symm rfl hT', θ₀, hθ₀, rfl⟩
    refine ⟨⟨T', rfl, rfl, rfl, hT'⟩, ?_, key q.tail htail θ hθ⟩
    have := neg_mem hsub
    rwa [neg_sub] at this

/-- Under the hypotheses of `exists_pair_mem_succ`, the character, as a pair, lies in the union
`S^{k+1}_n(𝔄)` of the sets `Ĉ(𝔄,k+1,γ)` over simple strata `[𝔄,n,k+1,γ]` on `L`. -/
theorem pair_mem_simpleCharacterPairsAt_succ (L : LatticeChain 𝒪[F] F V) (n : ℤ) (k : ℕ)
    (hk : (k : ℤ) + 1 < n) (S : Stratum 𝒪[F] F V) (hSL : S.chain = L) (hSn : S.n = n)
    (hSr : S.r = k) (hS : S.IsSimple) (q : S.DefiningSequenceChoice)
    {θ : simpleHGroup S.chain S.n S.b q.tail (k + 2) →* ℂˣ}
    (hθ : θ ∈ simpleCharacters ψF S.chain S.n S.b q.tail (k + 1)) :
    (⟨_, θ⟩ : CharacterPair G) ∈ simpleCharacterPairsAt ψF L n (k + 1) := by
  obtain ⟨T, -, hT⟩ := exists_pair_mem_succ ψF L n k hk S hSL hSn hSr hS q hθ
  exact Set.mem_iUnion.mpr ⟨T, hT⟩

/-- **BK93 (3.3.21).** Let `ψ_F` be trivial on `𝔭_F` and nontrivial on `𝔬_F`, let `k + 1 < n`
and let `[𝔄,n,k,β]` be a simple stratum on `L`. Assuming the group properties and the
restriction statement for simple characters, the restriction to `U^{k+2}(𝔄)` of a pair of
`Ĉ(𝔄,k,β)` is a pair of `Ĉ(𝔄,k+1,γ)` for a simple stratum `[𝔄,n,k+1,γ]` on `L` with
`γ ≡ β (mod 𝔓^{-(k+1)})`. -/
theorem exists_restrict_mem_succ (hGroups : SimpleStratumGroupPropertiesStatement.{uF, uV})
    (hRestr : SimpleCharacterRestrictionStatement.{uF, uV}) (hψ : IsBKAdditiveCharacter ψF)
    (L : LatticeChain 𝒪[F] F V) (n : ℤ) (k : ℕ) (hk : (k : ℤ) + 1 < n)
    (S : SimpleStratumAt L n k) (P : CharacterPair G) (hP : P ∈ simpleCharacterPairs ψF S.1 k) :
    ∃ T : SimpleStratumAt L n ((k + 1 : ℕ) : ℤ),
      T.1.b - S.1.b ∈ L.endFiltration (-((k + 1 : ℕ) : ℤ)) ∧
      P.restrict (L.unitFiltration (k + 2)) ∈ simpleCharacterPairs ψF T.1 (k + 1) := by
  obtain ⟨S, hSL, hSn, hSr, hS⟩ := S
  simp only [simpleCharacterPairs, Set.mem_iUnion, Set.mem_image] at hP
  obtain ⟨q, θ, hθ, rfl⟩ := hP
  have h0 : (0 : ℤ) ≤ S.r := by omega
  have hS0 := Stratum.isSimple_atDepthZero hS h0
  obtain ⟨hcarrier, -⟩ := hGroups F V (S.atDepthZero (h0.trans_lt S.r_lt_n)) rfl hS0
    (q.atDepthZero h0)
  obtain ⟨-, -, -, hd, -⟩ := hRestr F V ψF hψ (S.atDepthZero (h0.trans_lt S.r_lt_n)) rfl hS0
    (q.atDepthZero h0)
  have hθ' : simpleCharacterRestriction (S.atDepthZero (h0.trans_lt S.r_lt_n)) (q.atDepthZero h0)
      (Nat.le_succ k) θ ∈ simpleCharacters ψF S.chain S.n S.b q.tail (k + 1) := by
    have h : simpleCharacterRestriction (S.atDepthZero (h0.trans_lt S.r_lt_n)) (q.atDepthZero h0)
        (Nat.le_succ k) '' simpleCharacters ψF S.chain S.n S.b q.tail k =
        simpleCharacters ψF S.chain S.n S.b q.tail (k + 1) :=
      hd k (by change (k : ℤ) + 1 < S.n; omega)
    rw [← h]
    exact Set.mem_image_of_mem _ hθ
  have hdom : simpleHGroup S.chain S.n S.b q.tail (k + 1) ⊓ L.unitFiltration (k + 2) =
      simpleHGroup S.chain S.n S.b q.tail (k + 2) := by
    ext g
    have h1 : (simpleHGroup S.chain S.n S.b q.tail (k + 1) : Set G) =
        simpleHCarrier S.chain S.n S.b q.tail (k + 1) := (hcarrier (k + 1)).1
    have h2 : (simpleHGroup S.chain S.n S.b q.tail (k + 2) : Set G) =
        simpleHCarrier S.chain S.n S.b q.tail (k + 2) := (hcarrier (k + 2)).1
    rw [Subgroup.mem_inf, ← SetLike.mem_coe, h1, ← SetLike.mem_coe (p := simpleHGroup S.chain S.n S.b q.tail (k + 2)), h2]
    simp only [simpleHCarrier, Set.mem_ofPred_eq]
    rw [hSL]
    constructor
    · rintro ⟨⟨-, hg⟩, hg2⟩
      exact ⟨hg2, hg⟩
    · rintro ⟨hg2, hg⟩
      exact ⟨⟨L.unitFiltration_antitone (by omega) hg2, hg⟩, hg2⟩
  have hpair : CharacterPair.restrict (⟨simpleHGroup S.chain S.n S.b q.tail (k + 1), θ⟩ :
      CharacterPair G) (L.unitFiltration (k + 2)) = ⟨simpleHGroup S.chain S.n S.b q.tail (k + 2),
        simpleCharacterRestriction (S.atDepthZero (h0.trans_lt S.r_lt_n)) (q.atDepthZero h0)
          (Nat.le_succ k) θ⟩ :=
    CharacterPair.ext_of_eq hdom (fun g hP hQ => rfl)
  rw [hpair]
  exact exists_pair_mem_succ ψF L n k hk S hSL hSn hSr hS q hθ'

/-- **BK94 (2.2).** Let `ψ_F` be trivial on `𝔭_F` and nontrivial on `𝔬_F` and let `k + 1 < n`.
Assuming the group properties and the restriction statement for simple characters, restriction
to `U^{k+2}(𝔄)` maps the union `S^k_n(𝔄)` of the sets `Ĉ(𝔄,k,β)` over simple strata
`[𝔄,n,k,β]` on `L` into the union `S^{k+1}_n(𝔄)` at the successor depth. -/
theorem pairRestrictionAt (hGroups : SimpleStratumGroupPropertiesStatement.{uF, uV})
    (hRestr : SimpleCharacterRestrictionStatement.{uF, uV}) (hψ : IsBKAdditiveCharacter ψF)
    (L : LatticeChain 𝒪[F] F V) (n : ℤ) (k : ℕ) (hk : (k : ℤ) + 1 < n) :
    PairRestrictionAt ψF L n k := by
  intro P hP
  obtain ⟨S, hPS⟩ := Set.mem_iUnion.mp hP
  obtain ⟨T, -, hT⟩ := exists_restrict_mem_succ ψF hGroups hRestr hψ L n k hk S P hPS
  exact Set.mem_iUnion.mpr ⟨T, hT⟩

omit [TopologicalSpace F] [IsNonarchimedeanLocalField F] in
/-- A simple stratum at index `r` has critical depth larger than `r`. -/
theorem Stratum.IsSimple.r_lt_simpleCriticalDepth {S : Stratum 𝒪[F] F V} (hS : S.IsSimple) :
    (S.r : WithTop ℤ) < simpleCriticalDepth S.chain S.b := by
  have h := hS.2
  unfold simpleCriticalDepth
  cases hc : criticalExponent S.chain S.b with
  | bot => exact WithTop.coe_lt_top _
  | coe k =>
    rw [hc] at h
    have h' := WithBot.coe_lt_coe.mp h
    exact WithTop.coe_lt_coe.mpr (by omega)

/-- **BK94 p. 118.** For `ψ_F` trivial on `𝔭_F` and nontrivial on `𝔬_F` and simple strata
`[𝔄,n,m,β]` and `[𝔄,n,m,β']` on the same indexed chain with `β' ≡ β (mod 𝔓^{-m})`,
`Ĉ(𝔄,m,β) ⊆ Ĉ(𝔄,m,β')`; by symmetry `Ĉ(𝔄,m,β)` depends only on the equivalence class of
`[𝔄,n,m,β]`. -/
theorem simpleCharacterPairs_subset_of_sub_mem
    (hApprox : PureStratumSimpleApproximationStatement.{uF, uV})
    (hChoice : SimpleCharacterChoiceStatement.{uF, uV}) (hψ : IsBKAdditiveCharacter ψF)
    (S T : Stratum 𝒪[F] F V) (m : ℕ) (hSr : S.r = m) (hTr : T.r = m) (hS : S.IsSimple)
    (hT : T.IsSimple) (hchain : T.chain = S.chain) (hn : T.n = S.n)
    (hb : T.b - S.b ∈ S.chain.endFiltration (-(m : ℤ))) :
    simpleCharacterPairs ψF S m ⊆ simpleCharacterPairs ψF T m := by
  intro P hP
  simp only [simpleCharacterPairs, Set.mem_iUnion, Set.mem_image] at hP
  obtain ⟨q, θ, hθ, rfl⟩ := hP
  obtain ⟨q'', -, -⟩ := Stratum.exists_exact_definingSequenceChoice hApprox T hT
  have h0 : (0 : ℤ) ≤ S.r := by omega
  have hdepth := hS.r_lt_simpleCriticalDepth
  rw [hSr] at hdepth
  obtain ⟨hH, hC⟩ := (hChoice F V ψF hψ (S.atDepthZero (h0.trans_lt S.r_lt_n)) rfl
    (Stratum.isSimple_atDepthZero hS h0) (q.atDepthZero h0)).2 T (by rw [hchain]; rfl) hn hT
    (by omega) (by rw [hTr]; exact hdepth) (by rw [hTr]; exact hb) q'' m
    (by rw [hTr]; omega) (by have := S.r_lt_n; change (m : ℤ) < S.n; omega) hdepth
  change simpleHGroup S.chain S.n S.b q.tail (m + 1) =
    simpleHGroup T.chain T.n T.b q''.tail (m + 1) at hH
  change simpleCharacters ψF T.chain T.n T.b q''.tail m =
    characterSetTwist _ (simpleCharacters ψF S.chain S.n S.b q.tail m)
      (elementCharacter (traceCharacter ψF) (T.b - S.b)) at hC
  let θ'' : simpleHGroup T.chain T.n T.b q''.tail (m + 1) →* ℂˣ :=
    θ.comp (MulEquiv.subgroupCongr hH.symm).toMonoidHom
  have hθ'' : θ'' ∈ simpleCharacters ψF T.chain T.n T.b q''.tail m := by
    rw [hC]
    refine ⟨θ, hθ, fun g => ?_⟩
    obtain ⟨g, hg⟩ := g
    refine ⟨hg, by rw [hH]; exact hg, ?_⟩
    have hgU : g ∈ S.chain.unitFiltration (m + 1) := by
      have := simpleHGroup_le_unitFiltration T.chain T.n T.b q''.tail (m + 1) hg
      rwa [hchain] at this
    rw [elementCharacter_eq_one_of_depth S.chain ψF hψ hb (k := m + 1) (by push_cast; omega) hgU,
      mul_one]
    rfl
  refine Set.mem_iUnion.mpr ⟨q'', θ'', hθ'', ?_⟩
  exact CharacterPair.ext_of_eq (P := ⟨_, θ''⟩) (Q := ⟨_, θ⟩) hH.symm (fun g hP hQ => rfl)

omit [TopologicalSpace F] [IsNonarchimedeanLocalField F] in
/-- Two indexed lattice chains are equal when their lattices are equal at every index `i`. -/
theorem LatticeChain.ext_of_lattice {L M : LatticeChain 𝒪[F] F V}
    (h : ∀ i, L.lattice i = M.lattice i) : L = M := by
  cases L
  cases M
  congr
  funext i
  exact h i

omit [TopologicalSpace F] [IsNonarchimedeanLocalField F] in
/-- A unit of `𝔄` leaves the chain unchanged. -/
theorem LatticeChain.linearEquivMap_unit (L : LatticeChain 𝒪[F] F V) {u : G}
    (hu : u ∈ L.unitFiltration 0) :
    L.linearEquivMap (LinearMap.GeneralLinearGroup.toLinearEquiv u) = L := by
  refine LatticeChain.ext_of_lattice (fun i => ?_)
  ext x
  rw [LatticeChain.mem_linearEquivMap]
  constructor
  · intro h
    have h2 := L.mem_order.mp hu.1 i _ h
    rwa [show (u : A) ((LinearMap.GeneralLinearGroup.toLinearEquiv u).symm x) = x from
      LinearEquiv.apply_symm_apply (LinearMap.GeneralLinearGroup.toLinearEquiv u) x] at h2
  · intro h
    exact L.mem_order.mp hu.2.1 i x h

/-- **BK94 p. 118.** Let `V` be finite-dimensional, `ψ_F` trivial on `𝔭_F` and nontrivial on
`𝔬_F`, and `[𝔄,n,m,β]`, `[𝔄,n,m,β']` simple strata on `L`. If `u ∈ U(𝔄)` and
`β' ≡ u⁻¹ β u (mod 𝔓^{-m})`, conjugation by `u` carries `Ĉ(𝔄,m,β)` into `Ĉ(𝔄,m,β')`. -/
theorem simpleCharacterPairs_conj_mem [FiniteDimensional F V]
    (hApprox : PureStratumSimpleApproximationStatement.{uF, uV})
    (hConj : SimpleCharacterConjugationStatement.{uF, uV})
    (hChoice : SimpleCharacterChoiceStatement.{uF, uV}) (hψ : IsBKAdditiveCharacter ψF)
    (L : LatticeChain 𝒪[F] F V) (n : ℤ) (m : ℕ) (S T : SimpleStratumAt L n m) (u : G)
    (hu : u ∈ L.unitFiltration 0)
    (hST : T.1.b - ((↑u⁻¹ : A) * S.1.b * (u : A)) ∈ L.endFiltration (-(m : ℤ)))
    (P : CharacterPair G) (hP : P ∈ simpleCharacterPairs ψF S.1 m) :
    P.conj u ∈ simpleCharacterPairs ψF T.1 m := by
  obtain ⟨hSL, hSn, hSr, hS⟩ := S.2
  obtain ⟨hTL, hTn, hTr, hT⟩ := T.2
  obtain ⟨-, -, -, -, T', hT'chain, hT'n, hT'r, hT'b, hT'simple, -, hT'C, -, -⟩ :=
    hConj F V ψF hψ S.1 m hSr hS u⁻¹
  have hPT' : P.conj u ∈ simpleCharacterPairs ψF T' m := by
    rw [hT'C]
    exact ⟨P, hP, by rw [inv_inv]⟩
  have hL' : T'.chain = L := by
    rw [hT'chain, hSL]
    exact L.linearEquivMap_unit (inv_mem hu)
  have hb' : T'.b = (↑u⁻¹ : A) * S.1.b * (u : A) := by
    rw [hT'b]
    ext v
    rfl
  exact simpleCharacterPairs_subset_of_sub_mem ψF hApprox hChoice hψ T' T.1 m (hT'r.trans hSr)
    hTr hT'simple hT (hTL.trans hL'.symm) (hTn.trans (hSn.symm.trans hT'n.symm))
    (by rw [hb', hL']; exact hST) hPT'

end Premises

/-- The fibres of restriction at every depth below the top (BK94 (2.7)–(2.10), upper half):
over each pair at depth `k + 1`, the classes of the fibre inject into the classes of
simple strata refining the given stratum. -/
def SimpleCharacterFibreInjectionStatement : Prop :=
  ∀ (F : Type uF) [Field F] [ValuativeRel F] [TopologicalSpace F]
    [IsNonarchimedeanLocalField F] (V : Type uV) [AddCommGroup V] [Module F V]
    [FiniteDimensional F V] (ψF : AddChar F ℂ), IsBKAdditiveCharacter ψF →
    ∀ (L : LatticeChain 𝒪[F] F V) (n : ℤ) (k : ℕ), (k : ℤ) + 1 < n →
      FibreInjectionAt ψF L n k

/-- The cover of simple-character classes from the Library's simple-character statements
and the fibre injection. -/
theorem simpleCharacterClassCover_of_fibreInjection
    (hApprox : PureStratumSimpleApproximationStatement.{uF, uV})
    (hConj : SimpleCharacterConjugationStatement.{uF, uV})
    (hChoice : SimpleCharacterChoiceStatement.{uF, uV})
    (hGroups : SimpleStratumGroupPropertiesStatement.{uF, uV})
    (hRestr : SimpleCharacterRestrictionStatement.{uF, uV})
    (hFibre : SimpleCharacterFibreInjectionStatement.{uF, uV}) :
    SimpleCharacterClassCoverStatement.{uF, uV} := by
  intro F _ _ _ _ V _ _ _ ψF hψ L n m hm
  exact classCoverAt_of_premises ψF L n hψ m hm
    (fun S T u hu hST P hP => simpleCharacterPairs_conj_mem ψF hApprox hConj hChoice hψ L n m
      S T u hu hST P hP)
    (fun S => simpleCharacterPairs_nonempty ψF hApprox hRestr hψ S.1 S.2.2.2.2 m S.2.2.2.1)
    (fun k hk => pairRestrictionAt ψF hGroups hRestr hψ L n k hk)
    (fun k hk => hFibre F V ψF hψ L n k hk)

end Langlands.BushnellKutzko
