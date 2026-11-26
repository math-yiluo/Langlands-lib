import Langlands.BushnellKutzko.SimpleCharacterTranslationStatement
import Langlands.BushnellKutzko.SimpleCharacterCriticalTranslationStatement
import Langlands.BushnellKutzko.SimpleCharacterLoweringStatement
import Langlands.BushnellKutzko.SimpleCharacterTransferInputs
import Langlands.BushnellKutzko.SimpleCharacterRestrictionHigh
import Langlands.BushnellKutzko.SimpleCharacterPairsReindex

/-! # Reduction of the Translation Principle (BK94 (2.11) and §5, printed pp. 123, 132–133) -/

open ValuativeRel

noncomputable section

namespace Langlands.BushnellKutzko

universe uF uV uG

/-- The critical translation, the lowering theorem, the critical-approximation
twist, defining-sequence independence and pure-stratum approximation imply the
Translation Principle. -/
def SimpleCharacterTranslationReductionStatement : Prop :=
  SimpleCharacterCriticalTranslationStatement.{uF, uV} →
  SimpleCharacterLoweringStatement.{uF, uV} →
  SimpleCharacterRestrictionStatement.{uF, uV} →
  SimpleCharacterChoiceStatement.{uF, uV} →
  PureStratumSimpleApproximationStatement.{uF, uV} →
  SimpleCharacterTranslationStatement.{uF, uV}

section Pairs

variable {G : Type uG} [Group G]

/-- Multiply every character of a set of pairs by a fixed function, keeping its domain. -/
private def characterPairTwist (P : Set (CharacterPair G)) (t : G → ℂ) :
    Set (CharacterPair G) :=
  {Q | ∃ R ∈ P, R.1 = Q.1 ∧ characterAgreesOn Q.1 Q.2 R.2 t}

private theorem pair_eq_of_agrees {H H' : Subgroup G} (h : H = H') {θ : H →* ℂˣ}
    {θ' : H' →* ℂˣ} (hag : characterAgreesOn H' θ' θ (fun _ => 1)) :
    (⟨H', θ'⟩ : CharacterPair G) = ⟨H, θ⟩ := by
  subst h
  congr 1
  apply DFunLike.ext
  intro g
  obtain ⟨_, _, he⟩ := hag g
  exact Units.ext (by simpa only [mul_one] using he)

private theorem characterPairTwist_image (H : Subgroup G) (C : Set (H →* ℂˣ)) (t : G → ℂ) :
    characterPairTwist ((fun θ => (⟨H, θ⟩ : CharacterPair G)) '' C) t =
      (fun θ => (⟨H, θ⟩ : CharacterPair G)) '' characterSetTwist H C t := by
  ext Q
  obtain ⟨K, χ⟩ := Q
  constructor
  · rintro ⟨R, ⟨θ, hθ, rfl⟩, hK, hag⟩
    change H = K at hK
    subst hK
    exact ⟨χ, ⟨θ, hθ, hag⟩, rfl⟩
  · rintro ⟨χ', ⟨θ, hθ, hag⟩, heq⟩
    obtain ⟨rfl, hχ⟩ := Sigma.mk.inj_iff.mp heq
    obtain rfl := eq_of_heq hχ
    exact ⟨⟨H, θ⟩, ⟨θ, hθ, rfl⟩, rfl, hag⟩

private theorem characterPairTwist_congr {P : Set (CharacterPair G)} {t t' : G → ℂ}
    (h : ∀ R ∈ P, ∀ g ∈ R.1, t g = t' g) :
    characterPairTwist P t = characterPairTwist P t' := by
  ext Q
  constructor
  · rintro ⟨R, hR, hK, hag⟩
    refine ⟨R, hR, hK, fun g => ?_⟩
    obtain ⟨h₁, h₂, he⟩ := hag g
    exact ⟨h₁, h₂, by rw [← h R hR g h₂]; exact he⟩
  · rintro ⟨R, hR, hK, hag⟩
    refine ⟨R, hR, hK, fun g => ?_⟩
    obtain ⟨h₁, h₂, he⟩ := hag g
    exact ⟨h₁, h₂, by rw [h R hR g h₂]; exact he⟩

private theorem characterPairTwist_one (P : Set (CharacterPair G)) :
    characterPairTwist P (fun _ => 1) = P := by
  ext Q
  obtain ⟨K, χ⟩ := Q
  constructor
  · rintro ⟨⟨H, θ⟩, hR, hK, hag⟩
    change H = K at hK
    rw [pair_eq_of_agrees hK hag]
    exact hR
  · intro hQ
    exact ⟨⟨K, χ⟩, hQ, rfl, fun g => ⟨g.2, g.2, by simp⟩⟩

private theorem image_characterSetTwist_congr {H₀ H H' : Subgroup G} (C : Set (H₀ →* ℂˣ))
    (t : G → ℂ) (h : H = H') :
    (fun θ => (⟨H, θ⟩ : CharacterPair G)) '' characterSetTwist H C t =
      (fun θ => (⟨H', θ⟩ : CharacterPair G)) '' characterSetTwist H' C t := by
  subst h
  rfl

end Pairs

variable {F : Type uF} [Field F] [ValuativeRel F] {V : Type uV} [AddCommGroup V] [Module F V]

local notation "A" => Module.End F V
local notation "G" => (Module.End F V)ˣ

omit [ValuativeRel F] in
private theorem elementCharacter_add' (ψF : AddChar F ℂ) (β γ : A) (h : G) :
    elementCharacter (traceCharacter ψF) (β + γ) h =
      elementCharacter (traceCharacter ψF) β h * elementCharacter (traceCharacter ψF) γ h := by
  simp only [elementCharacter_apply, add_mul, AddChar.map_add_eq_mul]

variable [TopologicalSpace F] [IsNonarchimedeanLocalField F]

/-- With defining-sequence independence, the pairs are those of any one defining sequence. -/
private theorem simpleCharacterPairs_eq_image (hC : SimpleCharacterChoiceStatement.{uF, uV})
    (ψF : AddChar F ℂ) (hψ : IsBKAdditiveCharacter ψF) (S : Stratum 𝒪[F] F V)
    (h0 : 0 ≤ S.r) (hS : S.IsSimple) (q : S.DefiningSequenceChoice) (m : ℕ)
    (hm : (m : ℤ) < S.n) :
    simpleCharacterPairs ψF S m =
      (fun θ => (⟨simpleHGroup S.chain S.n S.b q.tail (m + 1), θ⟩ : CharacterPair G)) ''
        simpleCharacters ψF S.chain S.n S.b q.tail m := by
  apply le_antisymm
  · intro P hP
    simp only [simpleCharacterPairs, Set.mem_iUnion, Set.mem_image] at hP
    obtain ⟨q', θ', hθ', rfl⟩ := hP
    obtain ⟨hH, hCq⟩ := transfer_choice_comparison hC ψF hψ S h0 hS q q' m hm
    rw [hCq] at hθ'
    obtain ⟨θ, hθ, hag⟩ := hθ'
    exact ⟨θ, hθ, (pair_eq_of_agrees hH hag).symm⟩
  · intro P hP
    simp only [simpleCharacterPairs, Set.mem_iUnion]
    exact ⟨q, hP⟩

/-- The twist of a noncritical simple stratum by an equivalent upper stratum. -/
private theorem simpleCharacterPairs_twist_of_choice
    (hC : SimpleCharacterChoiceStatement.{uF, uV})
    (hApprox : PureStratumSimpleApproximationStatement.{uF, uV})
    (ψF : AddChar F ℂ) (hψ : IsBKAdditiveCharacter ψF) (R T : Stratum 𝒪[F] F V)
    (hc : R.chain = T.chain) (hn : R.n = T.n) (hR : R.IsSimple) (hT : T.IsSimple)
    (hT0 : 0 ≤ T.r) (hR0 : 0 ≤ R.r) (hRT : (R.r : WithTop ℤ) < simpleCriticalDepth T.chain T.b)
    (hsub : R.b - T.b ∈ T.chain.endFiltration (-R.r)) (k : ℕ)
    (hk₀ : R.r / 2 ≤ (k : ℤ)) (hk₁ : (k : ℤ) < T.n)
    (hk₂ : ((k : ℤ) : WithTop ℤ) < simpleCriticalDepth T.chain T.b) :
    simpleCharacterPairs ψF R k =
      characterPairTwist (simpleCharacterPairs ψF T k)
        (elementCharacter (traceCharacter ψF) (R.b - T.b)) := by
  obtain ⟨q, -, -⟩ := Stratum.exists_exact_definingSequenceChoice hApprox T hT
  obtain ⟨q', -, -⟩ := Stratum.exists_exact_definingSequenceChoice hApprox R hR
  have h := (hC F V ψF hψ (T.lowerIndex 0 hT0) rfl (hT.lowerIndex hT0) (q.lowerIndex hT0)).2 R
    (by rw [hc]; rfl) hn hR hR0 hRT hsub q' k hk₀ hk₁ hk₂
  dsimp only at h
  rw [q.lowerIndex_tail hT0] at h
  obtain ⟨hH, hCq⟩ := h
  rw [simpleCharacterPairs_eq_image hC ψF hψ T hT0 hT q k hk₁,
    simpleCharacterPairs_eq_image hC ψF hψ R hR0 hR q' k (hn ▸ hk₁), characterPairTwist_image,
    hCq]
  exact image_characterSetTwist_congr _ _ hH.symm

/-- The twist of a simple stratum by its critical approximation. -/
private theorem simpleCharacterPairs_twist_of_critical
    (hRes : SimpleCharacterRestrictionStatement.{uF, uV})
    (hC : SimpleCharacterChoiceStatement.{uF, uV})
    (hApprox : PureStratumSimpleApproximationStatement.{uF, uV})
    (ψF : AddChar F ℂ) (hψ : IsBKAdditiveCharacter ψF) (S T : Stratum 𝒪[F] F V)
    (hS0 : 0 ≤ S.r) (hT0 : 0 ≤ T.r) (hS : S.IsSimple) (hcrit : S.IsCriticalApproximation T)
    (k : ℕ) (hk₀ : T.r / 2 ≤ (k : ℤ)) (hk₁ : (k : ℤ) < T.r) :
    simpleCharacterPairs ψF S k =
      characterPairTwist (simpleCharacterPairs ψF T k)
        (elementCharacter (traceCharacter ψF) (S.b - T.b)) := by
  obtain ⟨hord, hn, hT, hk, -⟩ := id hcrit
  obtain ⟨q, -, -⟩ := Stratum.exists_exact_definingSequenceChoice hApprox S hS
  obtain ⟨q', -, -⟩ := Stratum.exists_exact_definingSequenceChoice hApprox T hT
  have hr : finiteCriticalDepth S.chain S.n S.b = T.r :=
    finiteCriticalDepth_of_criticalExponent_eq S.chain S.n T.r S.b hk
  have hkn : (k : ℤ) < S.n := hk₁.trans (hn ▸ T.r_lt_n)
  have h := (hRes F V ψF hψ (S.lowerIndex 0 hS0) rfl (hS.lowerIndex hS0) (q.lowerIndex hS0)).2.2.1
    T hcrit q' k (by change finiteCriticalDepth S.chain S.n S.b / 2 ≤ (k : ℤ); rw [hr]; exact hk₀)
    (by change (k : ℤ) < finiteCriticalDepth S.chain S.n S.b; rw [hr]; exact hk₁)
  dsimp only at h
  rw [q.lowerIndex_tail hS0] at h
  obtain ⟨hH, e, he⟩ := h
  have hne : ∀ g : G, elementCharacter (traceCharacter ψF) (S.b - T.b) g ≠ 0 :=
    fun g => ((traceCharacter ψF).val_isUnit _).ne_zero
  have hCS : simpleCharacters ψF S.chain S.n S.b q.tail k =
      characterSetTwist (simpleHGroup S.chain S.n S.b q.tail (k + 1))
        (simpleCharacters ψF T.chain T.n T.b q'.tail k)
        (elementCharacter (traceCharacter ψF) (S.b - T.b)) := by
    ext θ'
    constructor
    · intro hθ
      refine ⟨(e ⟨θ', hθ⟩).val, (e ⟨θ', hθ⟩).2, fun g => ?_⟩
      have hgH' : (g : G) ∈ simpleHGroup T.chain T.n T.b q'.tail (k + 1) := hH ▸ g.2
      obtain ⟨h₁, h₂, heq⟩ := he ⟨θ', hθ⟩ ⟨g, hgH'⟩
      refine ⟨h₂, h₁, ?_⟩
      have heq' : ((e ⟨θ', hθ⟩).val ⟨(g : G), h₁⟩ : ℂ) = (θ' ⟨(g : G), h₂⟩ : ℂ) *
          (elementCharacter (traceCharacter ψF) (S.b - T.b) g)⁻¹ := heq
      rw [heq', mul_assoc, inv_mul_cancel₀ (hne g), mul_one]
    · rintro ⟨η, hη, hag⟩
      let θ := e.symm ⟨η, hη⟩
      have heta : (e θ).val = η := congrArg Subtype.val (e.apply_symm_apply ⟨η, hη⟩)
      have hθ' : θ' = θ.val := by
        apply DFunLike.ext
        intro g
        apply Units.ext
        have hgH' : (g : G) ∈ simpleHGroup T.chain T.n T.b q'.tail (k + 1) := hH ▸ g.2
        obtain ⟨h₁, h₂, heq⟩ := he θ ⟨g, hgH'⟩
        obtain ⟨k₁, k₂, heq'⟩ := hag g
        have heq₂ : (η ⟨(g : G), h₁⟩ : ℂ) = (θ.val ⟨(g : G), h₂⟩ : ℂ) *
            (elementCharacter (traceCharacter ψF) (S.b - T.b) g)⁻¹ := by
          rw [← heta]
          exact heq
        change (θ' ⟨(g : G), k₁⟩ : ℂ) = (θ.val ⟨(g : G), h₂⟩ : ℂ)
        rw [heq', heq₂, mul_assoc, inv_mul_cancel₀ (hne g), mul_one]
      rw [hθ']
      exact θ.2
  rw [simpleCharacterPairs_eq_image hC ψF hψ S hS0 hS q k hkn,
    simpleCharacterPairs_eq_image hC ψF hψ T hT0 hT q' k (hk₁.trans T.r_lt_n),
    characterPairTwist_image, hCS]
  exact image_characterSetTwist_congr _ _ hH

omit [TopologicalSpace F] [IsNonarchimedeanLocalField F] in
private theorem simpleCharacterPairs_le_unitFiltration (ψF : AddChar F ℂ) (S : Stratum 𝒪[F] F V)
    (m : ℕ) : ∀ R ∈ simpleCharacterPairs ψF S m, R.1 ≤ S.chain.unitFiltration (m + 1) := by
  intro R hR
  simp only [simpleCharacterPairs, Set.mem_iUnion, Set.mem_image] at hR
  obtain ⟨q, θ, -, rfl⟩ := hR
  exact simpleHGroup_le_unitFiltration _ _ _ _ _

/-- The pairs of a simple stratum at level `m` are those of a simple stratum at level
`m+1` on the same chain, twisted by the difference of the elements. -/
private theorem simpleCharacterPairs_twist
    (hRes : SimpleCharacterRestrictionStatement.{uF, uV})
    (hC : SimpleCharacterChoiceStatement.{uF, uV})
    (hApprox : PureStratumSimpleApproximationStatement.{uF, uV})
    (ψF : AddChar F ℂ) (hψ : IsBKAdditiveCharacter ψF) {L : LatticeChain 𝒪[F] F V} {n : ℤ}
    {m : ℕ} (hmn : (m : ℤ) + 1 < n) (S : SimpleStratumAt L n m)
    (T : SimpleStratumAt L n ((m : ℤ) + 1))
    (hsub : S.1.b - T.1.b ∈ L.endFiltration (-((m : ℤ) + 1))) :
    simpleCharacterPairs ψF S.1 m =
      characterPairTwist (simpleCharacterPairs ψF T.1 m)
        (elementCharacter (traceCharacter ψF) (S.1.b - T.1.b)) := by
  obtain ⟨S, hSc, hSn, hSr, hS⟩ := S
  obtain ⟨T, hTc, hTn, hTr, hT⟩ := T
  dsimp only at hsub ⊢
  subst hSc hSn
  have hS0 : 0 ≤ S.r := by rw [hSr]; exact Int.natCast_nonneg m
  have hT0 : 0 ≤ T.r := by rw [hTr]; omega
  have hkS := hS.2
  rw [hSr] at hkS
  by_cases hcrit : criticalExponent S.chain S.b = ((-((m : ℤ) + 1) : ℤ) : WithBot ℤ)
  · have hca : S.IsCriticalApproximation T := by
      refine ⟨by rw [hTc], hTn, hT, by rw [hcrit, hTr], ?_⟩
      rw [hTr, ← neg_sub]
      exact neg_mem hsub
    exact simpleCharacterPairs_twist_of_critical hRes hC hApprox ψF hψ S T hS0 hT0 hS hca m
      (by rw [hTr]; omega) (by rw [hTr]; omega)
  · have hlt := criticalExponent_lt_succ_of_ne hkS hcrit
    let R : Stratum 𝒪[F] F V := { S with r := (m : ℤ) + 1, r_lt_n := hmn }
    have hR : R.IsSimple := ⟨hS.1, hlt⟩
    have hTdepth : (((m : ℤ) + 1 : ℤ) : WithTop ℤ) < simpleCriticalDepth T.chain T.b := by
      apply simpleCriticalDepth_gt_of_criticalExponent_lt
      have := hT.2
      rwa [hTr] at this
    rw [← simpleCharacterPairs_congr ψF (S := S) (S' := R) rfl rfl rfl hS hR m]
    exact simpleCharacterPairs_twist_of_choice hC hApprox ψF hψ R T hTc.symm hTn.symm hR hT hT0
      (by change (0 : ℤ) ≤ (m : ℤ) + 1; omega) hTdepth (by rw [hTc]; exact hsub) m
      (by change ((m : ℤ) + 1) / 2 ≤ (m : ℤ); omega) (by rw [hTn]; omega)
      (lt_trans (WithTop.coe_lt_coe.mpr (by omega)) hTdepth)

/-- **Reduction of BK94 (2.11).** -/
theorem simpleCharacterTranslationReduction :
    SimpleCharacterTranslationReductionStatement.{uF, uV} := by
  intro hCore hLow hRes hC hApprox F _ _ _ _ V _ _ _ ψF hψ L n m hmn T₁ T₂ S₁ hTC hS₁
  have hkS : criticalExponent L S₁.1.b < ((-(m : ℤ) : ℤ) : WithBot ℤ) := by
    have h := S₁.2.2.2.2.2
    rwa [S₁.2.1, S₁.2.2.2.1] at h
  by_cases hcrit : criticalExponent L S₁.1.b = ((-((m : ℤ) + 1) : ℤ) : WithBot ℤ)
  · -- the critical case: BK94 (5.3)–(5.6)
    obtain ⟨-, T₁', hT₁'eq, hT₁'C⟩ := hLow F V ψF hψ L n (m + 1) (by omega) T₁ T₂ hTC
    rw [Nat.add_sub_cancel] at hT₁'C
    have hsub₁ : S₁.1.b - T₁'.1.b ∈ L.endFiltration (-((m : ℤ) + 1)) := by
      have h := StratumEquivalence.sub_mem_of_equivalent hT₁'eq
      rw [T₁.2.1, T₁.2.2.2.1] at h
      rw [show S₁.1.b - T₁'.1.b = (S₁.1.b - T₁.1.b) - (T₁'.1.b - T₁.1.b) by abel]
      exact sub_mem hS₁ h
    obtain ⟨S₂, hS₂⟩ := hCore F V ψF hψ L n m T₁' T₂ S₁ hT₁'C hsub₁ hcrit
    have hsub₂ : S₂.1.b - T₂.1.b ∈ L.endFiltration (-((m : ℤ) + 1)) := by
      rw [show S₂.1.b - T₂.1.b = (S₂.1.b - (T₂.1.b + (S₁.1.b - T₁'.1.b))) +
          (S₁.1.b - T₁'.1.b) by abel]
      exact add_mem (L.endFiltration_antitone (by omega) hS₂) hsub₁
    refine ⟨S₂, hsub₂, ?_⟩
    rw [simpleCharacterPairs_twist hRes hC hApprox ψF hψ hmn S₂ T₂ hsub₂,
      simpleCharacterPairs_twist hRes hC hApprox ψF hψ hmn S₁ T₁' hsub₁, hT₁'C]
    apply characterPairTwist_congr
    intro R hR g hg
    have hU := simpleCharacterPairs_le_unitFiltration ψF T₂.1 m R hR hg
    rw [T₂.2.1] at hU
    rw [show S₂.1.b - T₂.1.b = (S₁.1.b - T₁'.1.b) +
        (S₂.1.b - (T₂.1.b + (S₁.1.b - T₁'.1.b))) by abel, elementCharacter_add',
      elementCharacter_eq_one_of_depth L ψF hψ hS₂ (by omega) hU, mul_one]
  · -- the noncritical case: BK93 (3.5.9) at level `m+1`
    have hlt := criticalExponent_lt_succ_of_ne hkS hcrit
    let R₁ : SimpleStratumAt L n ((m : ℤ) + 1) :=
      ⟨{ S₁.1 with r := (m : ℤ) + 1, r_lt_n := by rw [S₁.2.2.1]; exact hmn },
        S₁.2.1, S₁.2.2.1, rfl, S₁.2.2.2.2.1, by
          change criticalExponent S₁.1.chain S₁.1.b < ((-((m : ℤ) + 1) : ℤ) : WithBot ℤ)
          rw [S₁.2.1]
          exact hlt⟩
    have hT₁depth : (((m : ℤ) + 1 : ℤ) : WithTop ℤ) < simpleCriticalDepth T₁.1.chain T₁.1.b := by
      apply simpleCriticalDepth_gt_of_criticalExponent_lt
      have := T₁.2.2.2.2.2
      rwa [T₁.2.2.2.1] at this
    have hR₁C : simpleCharacterPairs ψF R₁.1 (m + 1) = simpleCharacterPairs ψF T₁.1 (m + 1) := by
      rw [simpleCharacterPairs_twist_of_choice hC hApprox ψF hψ R₁.1 T₁.1
        (S₁.2.1.trans T₁.2.1.symm) (S₁.2.2.1.trans T₁.2.2.1.symm) R₁.2.2.2.2 T₁.2.2.2.2
        (by rw [T₁.2.2.2.1]; omega) (by change (0 : ℤ) ≤ (m : ℤ) + 1; omega)
        (by rw [show R₁.1.r = (m : ℤ) + 1 from rfl]; exact hT₁depth)
        (by rw [T₁.2.1]; exact hS₁) (m + 1)
        (by change ((m : ℤ) + 1) / 2 ≤ ((m + 1 : ℕ) : ℤ); omega)
        (by rw [T₁.2.2.1]; push_cast; exact hmn)
        (by push_cast; exact hT₁depth)]
      rw [characterPairTwist_congr (t' := fun _ => 1), characterPairTwist_one]
      intro R hR g hg
      have hU := simpleCharacterPairs_le_unitFiltration ψF T₁.1 (m + 1) R hR hg
      rw [T₁.2.1] at hU
      exact elementCharacter_eq_one_of_depth L ψF hψ hS₁ (by push_cast; omega) hU
    obtain ⟨-, T₂', hT₂'eq, hT₂'C⟩ :=
      hLow F V ψF hψ L n (m + 1) (by omega) T₂ R₁ (hTC.symm.trans hR₁C.symm)
    rw [Nat.add_sub_cancel] at hT₂'C
    have hr : (m : ℤ) ≤ T₂'.1.r := by rw [T₂'.2.2.2.1]; push_cast; omega
    let S₂ : SimpleStratumAt L n m :=
      ⟨T₂'.1.lowerIndex m hr, T₂'.2.1, T₂'.2.2.1, rfl, T₂'.2.2.2.2.lowerIndex hr⟩
    refine ⟨S₂, ?_, ?_⟩
    · have h := StratumEquivalence.sub_mem_of_equivalent hT₂'eq
      rw [T₂.2.1, T₂.2.2.2.1] at h
      exact h
    · rw [simpleCharacterPairs_congr ψF (S := T₂'.1) (S' := S₂.1) rfl rfl rfl T₂'.2.2.2.2
        S₂.2.2.2.2 m, hT₂'C,
        simpleCharacterPairs_congr ψF (S := S₁.1) (S' := R₁.1) rfl rfl rfl S₁.2.2.2.2
          R₁.2.2.2.2 m]

end Langlands.BushnellKutzko
