import Langlands.BushnellKutzko.SimpleCharacterCoreRestriction

/-! # A common restriction depth for two core approximations -/

open ValuativeRel
open scoped Pointwise

namespace Langlands.BushnellKutzko

universe uF uV uG

section Transport

variable {G : Type uG} [Group G] {H K H' K' : Subgroup G}

private def castCharacter (h : H = H') (θ : H →* ℂˣ) : H' →* ℂˣ :=
  Eq.ndrec (motive := fun J : Subgroup G => J →* ℂˣ) θ h

private theorem castCharacter_mem (h : H = H') (C : Set (H →* ℂˣ)) (θ : H' →* ℂˣ)
    (hθ : θ ∈ transportCharacterSet h C) : castCharacter h.symm θ ∈ C := by
  cases h
  exact hθ

private theorem castCharacter_restriction_intertwining (h : H = H') (hk : K = K')
    (i : K ≤ H) (i' : K' ≤ H') (θ : H' →* ℂˣ) :
    characterSelfIntertwining ((castCharacter h.symm θ).comp (Subgroup.inclusion i)) =
      characterSelfIntertwining (θ.comp (Subgroup.inclusion i')) := by
  cases h
  cases hk
  rfl

private theorem castCharacter_ratio_intertwining (h : H = H') (χ θ : H' →* ℂˣ) :
    characterSelfIntertwining (castCharacter h.symm χ / castCharacter h.symm θ) =
      characterSelfIntertwining (χ / θ) := by
  cases h
  rfl

private theorem selfIntertwining_eq_of_agreesOn (h : H = K) {χ : H →* ℂˣ} {η : K →* ℂˣ}
    (ha : characterAgreesOn H χ η (fun _ => 1)) :
    characterSelfIntertwining χ = characterSelfIntertwining η := by
  cases h
  have heq : χ = η := by
    ext g
    obtain ⟨_, _, he⟩ := ha g
    simpa only [mul_one] using he
  rw [heq]

private theorem characterAgreesOn_div_of_same_twist {χ θ : H →* ℂˣ} {χ₀ θ₀ : K →* ℂˣ}
    {t : G → ℂ} (ha : characterAgreesOn H χ χ₀ t) (hb : characterAgreesOn H θ θ₀ t) :
    characterAgreesOn H (χ / θ) (χ₀ / θ₀) (fun _ => 1) := by
  intro g
  obtain ⟨hH, hK, hχ⟩ := ha g
  obtain ⟨_, _, hθ⟩ := hb g
  refine ⟨hH, hK, ?_⟩
  have ht : t g ≠ 0 := by
    intro hz
    rw [hz, mul_zero] at hχ
    exact Units.ne_zero _ hχ
  simp only [MonoidHom.div_apply, Units.val_div_eq_div_val, mul_one]
  rw [hχ, hθ, mul_div_mul_right _ _ ht]

/-- A common pointwise conjugation multiplier cancels in the quotient character. -/
theorem characterSelfIntertwining_div_of_common_multiplier {χ θ : H →* ℂˣ} {a : G}
    {t : G → ℂ}
    (hχ : ∀ (g : H) (hg : a * (g : G) * a⁻¹ ∈ H), (χ ⟨_, hg⟩ : ℂ) = (χ g : ℂ) * t g)
    (hθ : ∀ (g : H) (hg : a * (g : G) * a⁻¹ ∈ H), (θ ⟨_, hg⟩ : ℂ) = (θ g : ℂ) * t g) :
    a ∈ characterSelfIntertwining (χ / θ) := by
  intro g hg
  have hχg := hχ g hg
  have ht : t g ≠ 0 := by
    intro hz
    rw [hz, mul_zero] at hχg
    exact Units.ne_zero _ hχg
  apply Units.ext
  simp only [MonoidHom.div_apply, Units.val_div_eq_div_val]
  rw [hχg, hθ g hg, mul_div_mul_right _ _ ht]

end Transport

variable {F : Type uF} [Field F] [ValuativeRel F] [TopologicalSpace F]
  [IsNonarchimedeanLocalField F] {V : Type uV} [AddCommGroup V] [Module F V]

local notation "A" => Module.End F V
local notation "G" => (Module.End F V)ˣ
local notation "Hc(" S "," q "," m ")" => simpleHGroup (Stratum.chain S) (Stratum.n S) (Stratum.b S)
  (Stratum.DefiningSequenceChoice.tail q) (m + 1)
local notation "Cc(" ψ "," S "," q "," m ")" => simpleCharacters ψ (Stratum.chain S) (Stratum.n S)
  (Stratum.b S) (Stratum.DefiningSequenceChoice.tail q) m

/-- Cancellation form of the successor conjugation calculation of BK93 (3.3.9). -/
def SimpleCharacterRatioIntertwiningStatement : Prop :=
  ∀ (F : Type uF) [Field F] [ValuativeRel F] [TopologicalSpace F]
    [IsNonarchimedeanLocalField F] (V : Type uV) [AddCommGroup V] [Module F V]
    (ψF : AddChar F ℂ), IsBKAdditiveCharacter ψF →
    ∀ (S : Stratum 𝒪[F] F V), S.r = 0 → S.IsSimple → ∀ q : S.DefiningSequenceChoice,
    ∀ m t : ℕ, (m : ℤ) < S.n → (t : ℤ) < S.n →
      ((m : ℤ) : WithTop ℤ) < simpleCriticalDepth S.chain S.b →
      ((t : ℤ) : WithTop ℤ) < simpleCriticalDepth S.chain S.b → t / 2 ≤ m →
      ∀ χ ∈ Cc(ψF, S, q, m), ∀ θ ∈ Cc(ψF, S, q, m),
        let Y := simpleCharacterIntertwiningFactor S q t
        Y * (centralizerUnitGroup S.b : Set (Module.End F V)ˣ) * Y ⊆ characterSelfIntertwining (χ / θ)

/-- The successor conjugation formula implies the ratio intertwining comparison. -/
theorem simpleCharacterRatioIntertwining_of_covariance
    (hcov : ∀ (F : Type uF) [Field F] [ValuativeRel F] [TopologicalSpace F]
      [IsNonarchimedeanLocalField F] (V : Type uV) [AddCommGroup V] [Module F V]
      (ψF : AddChar F ℂ), IsBKAdditiveCharacter ψF →
      ∀ (S : Stratum 𝒪[F] F V), S.r = 0 → S.IsSimple → ∀ q : S.DefiningSequenceChoice,
      ∀ m t : ℕ, (m : ℤ) < S.n → (t : ℤ) < S.n →
        ((m : ℤ) : WithTop ℤ) < simpleCriticalDepth S.chain S.b →
        ((t : ℤ) : WithTop ℤ) < simpleCriticalDepth S.chain S.b → t / 2 ≤ m →
        ∀ θ ∈ Cc(ψF, S, q, m),
          let Y := simpleCharacterIntertwiningFactor S q t
          ∀ a ∈ Y * (centralizerUnitGroup S.b : Set (Module.End F V)ˣ) * Y,
            ∀ (g : Hc(S, q, m)) (hg : a * (g : (Module.End F V)ˣ) * a⁻¹ ∈ Hc(S, q, m)),
              (θ ⟨_, hg⟩ : ℂ) = (θ g : ℂ) *
                elementCharacter (traceCharacter ψF)
                  ((↑a⁻¹ : Module.End F V) * S.b * (a : Module.End F V) - S.b) g) :
    SimpleCharacterRatioIntertwiningStatement.{uF, uV} := by
  intro F _ _ _ _ V _ _ ψF hψ S hr hS q m t hm ht hcm hct hhalf χ hχ θ hθ Y a ha
  exact characterSelfIntertwining_div_of_common_multiplier
    (hcov F V ψF hψ S hr hS q m t hm ht hcm hct hhalf χ hχ a ha)
    (hcov F V ψF hψ S hr hS q m t hm ht hcm hct hhalf θ hθ a ha)

omit [TopologicalSpace F] [IsNonarchimedeanLocalField F] in
private theorem lt_simpleCriticalDepth_of_lt_finite (L : LatticeChain 𝒪[F] F V) (n : ℤ) (b : A)
    (k : ℤ) (hk : k < finiteCriticalDepth L n b) : (k : WithTop ℤ) < simpleCriticalDepth L b := by
  cases h : criticalExponent L b using WithBot.recBotCoe with
  | bot => simp [simpleCriticalDepth, h]
  | coe j =>
    have he : simpleCriticalDepth L b = ((-j : ℤ) : WithTop ℤ) := by
      rw [simpleCriticalDepth, h]
    rw [he, WithTop.coe_lt_coe]
    have hf : finiteCriticalDepth L n b = -j := by
      rw [finiteCriticalDepth, he]
      rfl
    rwa [← hf]

private theorem simpleHGroup_eq_at_higher_of_eq
    (hgroups : SimpleStratumGroupPropertiesStatement.{uF, uV})
    {S T : Stratum 𝒪[F] F V} (q : S.DefiningSequenceChoice) (q' : T.DefiningSequenceChoice)
    (hr : S.r = 0) (hr' : T.r = 0) (hS : S.IsSimple) (hT : T.IsSimple)
    (horder : T.chain.order = S.chain.order)
    {m k : ℕ} (hmk : m ≤ k) (h : Hc(S, q, m) = Hc(T, q', m)) : Hc(S, q, k) = Hc(T, q', k) := by
  have hi (R : Stratum 𝒪[F] F V) (p : R.DefiningSequenceChoice) (hr₀ : R.r = 0) (hR : R.IsSimple) :
      Hc(R, p, m) ⊓ R.chain.unitFiltration (k + 1) = Hc(R, p, k) := by
    have hc := (hgroups F V R hr₀ hR p).1
    ext g
    change (g ∈ (Hc(R, p, m) : Set G) ∧ g ∈ R.chain.unitFiltration (k + 1)) ↔
      g ∈ (Hc(R, p, k) : Set G)
    rw [(hc (m + 1)).1, (hc (k + 1)).1]
    exact ⟨fun h₁ => ⟨h₁.2, h₁.1.2⟩,
      fun h₁ => ⟨⟨R.chain.unitFiltration_antitone (Nat.succ_le_succ hmk) h₁.1, h₁.2⟩, h₁.1⟩⟩
  rw [← hi S q hr hS, ← hi T q' hr' hT, h, LatticeChain.unitFiltration_eq_of_order_eq horder]

private theorem core_restriction_intertwines_ratio
    (hgroups : SimpleStratumGroupPropertiesStatement.{uF, uV})
    (hrestriction : SimpleCharacterRestrictionStatement.{uF, uV})
    (hintertwining : SimpleCharacterIntertwiningStatement.{uF, uV})
    (hratios : SimpleCharacterRatioIntertwiningStatement.{uF, uV})
    {ψF : AddChar F ℂ} (hψ : IsBKAdditiveCharacter ψF)
    {S : Stratum 𝒪[F] F V} {q : S.DefiningSequenceChoice} {m k : ℕ}
    (hS : S.IsSimple) (hr : 0 ≤ S.r) (core : SimpleCharacterCore ψF S q m)
    (hmk : m ≤ k) (hdepth : core.stratum.r ≤ (k : ℤ)) (hkn : (k : ℤ) < S.n)
    (hcrit : ((k : ℤ) : WithTop ℤ) < simpleCriticalDepth core.stratum.chain core.stratum.b)
    (hhalf : k / 2 ≤ m) {χ θ : Hc(S, q, m) →* ℂˣ}
    (hχ : χ ∈ Cc(ψF, S, q, m)) (hθ : θ ∈ Cc(ψF, S, q, m)) :
    characterSelfIntertwining (simpleCharacterRestriction S q hmk θ) ⊆ characterSelfIntertwining (χ / θ) := by
  obtain ⟨χ₀, hχ₀, hagχ⟩ := core.twist.1 χ hχ
  obtain ⟨θ₀, hθ₀, hagθ⟩ := core.twist.1 θ hθ
  have haRatio := characterAgreesOn_div_of_same_twist hagχ hagθ
  have hsetRatio := selfIntertwining_eq_of_agreesOn core.domain_eq haRatio
  obtain ⟨ξ, hξ, hagξ⟩ := core.restriction_agrees_on_core hgroups hrestriction hψ hS hr hmk hdepth hkn hθ
  have hset := selfIntertwining_eq_of_agreesOn (core.domain_eq_of_le hgroups hS hr hmk) hagξ
  let T := core.stratum
  let hrT := hr.trans core.depth_le
  let T₀ := T.atDepthZero (hrT.trans_lt T.r_lt_n)
  let q₀ := core.sequence.atDepthZero hrT
  have hkT : (k : ℤ) < T.n := core.level_eq.symm ▸ hkn
  have hmT : (m : ℤ) < T.n := by omega
  have hmCrit : ((m : ℤ) : WithTop ℤ) < simpleCriticalDepth T.chain T.b := by
    exact (show ((m : ℤ) : WithTop ℤ) ≤ ((k : ℤ) : WithTop ℤ) by exact_mod_cast hmk).trans_lt hcrit
  have hT₀ := Stratum.isSimple_atDepthZero core.isSimple hrT
  have hI := (hintertwining F V ψF hψ T₀ rfl hT₀ q₀ k hkT hcrit ξ hξ).1
  have hratio := hratios F V ψF hψ T₀ rfl hT₀ q₀ m k hmT hkT hmCrit hcrit hhalf χ₀ hχ₀ θ₀ hθ₀
  intro g hg
  have hg' := hset ▸ hg
  exact hsetRatio.symm ▸ hratio (hI ▸ hg')

/-- A restriction at `2*m+1` works simultaneously for both cores. -/
theorem simpleCharacterCoreComparison_of_ratios
    (hlattices : SimpleStratumLatticePropertiesStatement.{uF, uV})
    (hgroups : SimpleStratumGroupPropertiesStatement.{uF, uV})
    (hrestriction : SimpleCharacterRestrictionStatement.{uF, uV})
    (hintertwining : SimpleCharacterIntertwiningStatement.{uF, uV})
    (hratios : SimpleCharacterRatioIntertwiningStatement.{uF, uV}) :
    SimpleCharacterCoreComparisonStatement.{uF, uV} := by
  intro F _ _ _ _ V _ _ ψF hψ S T q q' hr hr' hS hT horder hn m hm h C D θ hθ
  have hs : 0 ≤ S.r := by omega
  have ht : 0 ≤ T.r := by omega
  have hmT : (m : ℤ) < T.n / 2 := hn.symm ▸ hm
  obtain ⟨core, hcore⟩ := exists_simpleCharacterCore_with_depth_bound hlattices hrestriction ψF hψ q hS hs m hm
  obtain ⟨core', hcore'⟩ := exists_simpleCharacterCore_with_depth_bound hlattices hrestriction ψF hψ q' hT ht m hmT
  let k := 2 * m + 1
  have hmk : m ≤ k := by omega
  have hk : (k : ℤ) < S.n := by omega
  have hk' : (k : ℤ) < T.n := hn.symm ▸ hk
  have hhalf : k / 2 ≤ m := by omega
  have hd : core.stratum.r ≤ (k : ℤ) := by omega
  have hd' : core'.stratum.r ≤ (k : ℤ) := by omega
  have hcrit : ((k : ℤ) : WithTop ℤ) < simpleCriticalDepth core.stratum.chain core.stratum.b := by
    apply lt_simpleCriticalDepth_of_lt_finite _ core.stratum.n
    have := core.below_cutoff
    omega
  have hcrit' : ((k : ℤ) : WithTop ℤ) < simpleCriticalDepth core'.stratum.chain core'.stratum.b := by
    apply lt_simpleCriticalDepth_of_lt_finite _ core'.stratum.n
    have := core'.below_cutoff
    omega
  let θS := castCharacter h.symm θ
  have hθS : θS ∈ Cc(ψF, S, q, m) := castCharacter_mem h _ θ hθ.1
  have hkdom := simpleHGroup_eq_at_higher_of_eq hgroups q q' hr hr' hS hT horder hmk h
  have hset : characterSelfIntertwining (simpleCharacterRestriction S q hmk θS) =
      characterSelfIntertwining (simpleCharacterRestriction T q' hmk θ) :=
    castCharacter_restriction_intertwining h hkdom _ _ θ
  refine ⟨core, core', k, hmk, ?_, ?_, ?_⟩
  · change (centralizerUnitGroup core.stratum.b : Set (Module.End F V)ˣ) ⊆
      characterSelfIntertwining (simpleCharacterRestriction T q' hmk θ)
    rw [← hset]
    exact core.centralizer_subset_intertwining_restriction hgroups hrestriction hintertwining hψ hS hs
      hmk hd hk hcrit hθS
  · exact core'.centralizer_subset_intertwining_restriction hgroups hrestriction hintertwining hψ hT ht
      hmk hd' hk' hcrit' hθ.2
  · intro χ hχ
    rcases hχ with hχ | hχ
    · have hχS : castCharacter h.symm χ ∈ Cc(ψF, S, q, m) := castCharacter_mem h _ χ hχ
      have he := core_restriction_intertwines_ratio hgroups hrestriction hintertwining hratios hψ hS hs core
        hmk hd hk hcrit hhalf hχS hθS
      rw [hset, castCharacter_ratio_intertwining h χ θ] at he
      exact he
    · exact core_restriction_intertwines_ratio hgroups hrestriction hintertwining hratios hψ hT ht core'
        hmk hd' hk' hcrit' hhalf hχ hθ.2

/-- Coherence follows from the lattice and group formulas, restriction,
self-intertwining, relative determinant factorization and ratio intertwining. -/
def SimpleCharacterCoherenceFromRatiosStatement : Prop :=
  SimpleStratumLatticePropertiesStatement.{uF, uV} → SimpleStratumGroupPropertiesStatement.{uF, uV} →
  SimpleCharacterRestrictionStatement.{uF, uV} → SimpleCharacterIntertwiningStatement.{uF, uV} →
  SimpleCharacterCentralizerDeterminantStatement.{uF, uV} →
  SimpleCharacterRatioIntertwiningStatement.{uF, uV} → SimpleCharacterCoherenceStatement.{uF, uV}

theorem simpleCharacterCoherenceFromRatios : SimpleCharacterCoherenceFromRatiosStatement.{uF, uV} :=
  fun hlattices hgroups hrestriction hintertwining hdet hratios =>
    simpleCharacterCoherenceCoreReduction hgroups hrestriction hdet
      (simpleCharacterCoreComparison_of_ratios hlattices hgroups hrestriction hintertwining hratios)

end Langlands.BushnellKutzko
