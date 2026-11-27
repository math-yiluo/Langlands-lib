import Langlands.BushnellKutzko.SimpleCharacterLoweringGroups
import Langlands.BushnellKutzko.SimpleCharacterCoherenceStatement
import Langlands.BushnellKutzko.SimpleCharacterInvariantsStatement
import Langlands.BushnellKutzko.SimpleCharacterTransferSequences
import Langlands.BushnellKutzko.PureStratumApproximationCandidateBound
import Langlands.BushnellKutzko.SimpleCharacterCentralizerDeterminant

/-! # Simple characters one step below a common depth -/

noncomputable section

open ValuativeRel
open scoped Pointwise

namespace Langlands.BushnellKutzko

universe u v uF uV

section Characters

variable {K : Type*} [Group K]

/-- An element intertwining two characters on the same group intertwines their quotient. -/
theorem mem_characterSelfIntertwining_div_of_mem {H : Subgroup K} {χ φ : H →* ℂˣ} {a : K}
    (hχ : a ∈ characterSelfIntertwining χ) (hφ : a ∈ characterSelfIntertwining φ) :
    a ∈ characterSelfIntertwining (χ / φ) := by
  intro g hg
  rw [MonoidHom.div_apply, MonoidHom.div_apply, hχ g hg, hφ g hg]

/-- Multiplying an intertwining element on both sides by normalizing elements gives an
intertwining element. -/
theorem mul_mul_mem_characterSelfIntertwining {H : Subgroup K} {χ : H →* ℂˣ} {a b c : K}
    (ha : a ∈ characterNormalizer χ) (hb : b ∈ characterSelfIntertwining χ)
    (hc : c ∈ characterNormalizer χ) : a * b * c ∈ characterSelfIntertwining χ := by
  intro h hh
  have hc' : c * (h : K) * c⁻¹ ∈ H := (Subgroup.mem_normalizer_iff.mp hc.1 h).mp h.2
  have he : a * b * c * (h : K) * (a * b * c)⁻¹ =
      a * (b * (c * (h : K) * c⁻¹) * b⁻¹) * a⁻¹ := by group
  have hb' : b * (c * (h : K) * c⁻¹) * b⁻¹ ∈ H := by
    rw [he] at hh
    exact (Subgroup.mem_normalizer_iff.mp ha.1 _).mpr hh
  have e₁ : χ ⟨_, hh⟩ = χ ⟨_, (Subgroup.mem_normalizer_iff.mp ha.1 _).mp hb'⟩ :=
    congrArg χ (Subtype.ext he)
  rw [e₁, ha.2 ⟨_, hb'⟩, hb ⟨_, hc'⟩ hb', hc.2 h hc']

/-- Equal subgroups carrying pointwise agreeing characters give the same intertwining set. -/
theorem characterSelfIntertwining_eq_of_agree {H₁ H₂ : Subgroup K} (h : H₁ = H₂)
    (χ₁ : H₁ →* ℂˣ) (χ₂ : H₂ →* ℂˣ) (hag : characterAgreesOn H₁ χ₁ χ₂ (fun _ => 1)) :
    characterSelfIntertwining χ₁ = characterSelfIntertwining χ₂ := by
  subst h
  have : χ₁ = χ₂ := by
    ext g
    obtain ⟨h₁, h₂, e⟩ := hag g
    rw [mul_one] at e
    exact e
  rw [this]

/-- Restricting a character along an equality of subgroups keeps its intertwining set. -/
theorem characterSelfIntertwining_comp_inclusion {H₁ H₂ : Subgroup K} (h : H₁ = H₂)
    (φ : H₂ →* ℂˣ) :
    characterSelfIntertwining (φ.comp (Subgroup.inclusion h.le)) = characterSelfIntertwining φ := by
  subst h
  rfl

/-- A character in the second set whose restriction lies in the first set makes the
transported sets meet. -/
theorem characterSet_ndrec_inter_nonempty {H₁ H₂ : Subgroup K} (h : H₁ = H₂) {C₁ : Set (H₁ →* ℂˣ)}
    {C₂ : Set (H₂ →* ℂˣ)} {φ : H₂ →* ℂˣ} (hφ₂ : φ ∈ C₂)
    (hφ₁ : φ.comp (Subgroup.inclusion h.le) ∈ C₁) :
    (Eq.ndrec (motive := fun L : Subgroup K => Set (L →* ℂˣ)) C₁ h ∩ C₂).Nonempty := by
  subst h
  exact ⟨φ, hφ₁, hφ₂⟩

/-- Equality of a transported character set with a second set gives the two-sided
correspondence with trivial twist. -/
theorem characterSetTwistCorrespondence_of_ndrec_eq {H₁ H₂ : Subgroup K} (h : H₁ = H₂)
    {C₁ : Set (H₁ →* ℂˣ)} {C₂ : Set (H₂ →* ℂˣ)}
    (hC : Eq.ndrec (motive := fun L : Subgroup K => Set (L →* ℂˣ)) C₁ h = C₂) :
    CharacterSetTwistCorrespondence C₁ C₂ (fun _ => 1) := by
  subst h
  subst hC
  have hself (χ : H₁ →* ℂˣ) : characterAgreesOn H₁ χ χ (fun _ => 1) :=
    fun g => ⟨g.2, g.2, (mul_one _).symm⟩
  exact ⟨fun χ hχ => ⟨χ, hχ, hself χ⟩, fun χ hχ => ⟨χ, hχ, hself χ⟩⟩

end Characters

variable {F : Type u} [Field F] [ValuativeRel F] [TopologicalSpace F]
  [IsNonarchimedeanLocalField F] {V : Type v} [AddCommGroup V] [Module F V]

local notation "A" => Module.End F V
local notation "G" => (Module.End F V)ˣ

namespace Stratum

/-- Lower the index of the initial stratum and of the first term of a defining sequence,
keeping every element. The tail is definitionally unchanged. -/
def DefiningSequenceChoice.atIndex {S : Stratum 𝒪[F] F V} (q : S.DefiningSequenceChoice)
    {r : ℤ} (hr : r ≤ S.r) : (S.lowerIndex r hr).DefiningSequenceChoice := by
  obtain ⟨hPure, hTerms, _, hFirstDepth, hMono, hStep, hLast, hDerived⟩ := q.isDefiningSequence
  have hle : r ≤ (q.terms 0).r := hFirstDepth.symm ▸ hr
  let terms := Fin.cons ((q.terms 0).lowerIndex r hle)
    (α := fun _ => Stratum 𝒪[F] F V) (fun j : Fin q.steps => q.terms j.succ)
  have hElement (j : Fin (q.steps + 1)) : (terms j).b = (q.terms j).b := by
    refine Fin.cases ?_ (fun _ => ?_) j <;> rfl
  have hLater (j : Fin (q.steps + 1)) : j ≠ 0 → terms j = q.terms j := by
    refine Fin.cases (fun h => (h rfl).elim) (fun _ _ => rfl) j
  refine ⟨q.steps, terms, ⟨hPure, ?_, ?_, rfl, ?_, ?_, ?_, ?_⟩, q.firstElement⟩
  · refine Fin.cases ?_ (fun j => hTerms j.succ)
    exact ⟨(hTerms 0).1, (hTerms 0).2.1, (hTerms 0).2.2.lowerIndex hle⟩
  · unfold Equivalent coset
    simp only [terms, Fin.cons_zero, Stratum.lowerIndex, q.firstElement]
    rw [LatticeChain.endFiltration_eq_of_order_eq (hTerms 0).1]
  · rw [Fin.strictMono_iff_lt_succ]
    intro j
    change (terms j.castSucc).r < (q.terms j.succ).r
    by_cases hj : j.castSucc = 0
    · have hlt := hMono (Fin.castSucc_lt_succ (i := j))
      rw [hj] at hlt ⊢
      exact hle.trans_lt hlt
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

@[simp] theorem DefiningSequenceChoice.tail_atIndex {S : Stratum 𝒪[F] F V}
    (q : S.DefiningSequenceChoice) {r : ℤ} (hr : r ≤ S.r) : (q.atIndex hr).tail = q.tail := rfl

end Stratum

omit [TopologicalSpace F] [IsNonarchimedeanLocalField F] in
/-- A depth below the finite critical depth is below the critical depth. -/
theorem lt_simpleCriticalDepth_of_lt (L : LatticeChain 𝒪[F] F V) (n : ℤ) (b : A) {k : ℤ}
    (hk : k < finiteCriticalDepth L n b) : (k : WithTop ℤ) < simpleCriticalDepth L b := by
  cases hd : simpleCriticalDepth L b with
  | top => exact WithTop.coe_lt_top _
  | coe d =>
    have hrd : finiteCriticalDepth L n b = d := by simp [finiteCriticalDepth, hd]
    exact WithTop.coe_lt_coe.mpr (by omega)

omit [TopologicalSpace F] [IsNonarchimedeanLocalField F] in
theorem simpleCharacterIntertwiningFactor_one_mem (S : Stratum 𝒪[F] F V)
    (q : S.DefiningSequenceChoice) (m : ℕ) : (1 : G) ∈ simpleCharacterIntertwiningFactor S q m := by
  unfold simpleCharacterIntertwiningFactor
  split_ifs
  · rfl
  · simp only [Set.mem_ofPred_eq, Units.val_one, sub_self]
    exact zero_mem _

/-- When `2(m+1) ≤ r = finiteCriticalDepth L n β`, the outer factor at depth `m+1` lies in the
outer factor at depth `m`. -/
theorem simpleCharacterIntertwiningFactor_succ_subset (S : Stratum 𝒪[F] F V)
    (q : S.DefiningSequenceChoice) (m : ℕ)
    (hm : 2 * ((m + 1 : ℕ) : ℤ) ≤ finiteCriticalDepth S.chain S.n S.b) :
    simpleCharacterIntertwiningFactor S q (m + 1) ⊆ simpleCharacterIntertwiningFactor S q m := by
  by_cases hb : elementAlgebra S.b = ⊥
  · unfold simpleCharacterIntertwiningFactor
    rw [ite_eq_left hb, ite_eq_left hb]
  · rw [simpleCharacterIntertwiningFactor_eq_simpleJLayer S q (m + 1) hb hm]
    intro g hg
    unfold simpleCharacterIntertwiningFactor
    rw [ite_eq_right hb]
    exact Submodule.mem_sup_right hg

/-- Elements of the outer factor normalize every simple character at the same depth. -/
theorem simpleCharacterIntertwiningFactor_subset_normalizer
    (hint : SimpleCharacterIntertwiningStatement.{u, v})
    (ψF : AddChar F ℂ) (hψ : IsBKAdditiveCharacter ψF)
    (S : Stratum 𝒪[F] F V) (h0 : S.r = 0) (hs : S.IsSimple) (q : S.DefiningSequenceChoice)
    (m : ℕ) (hmn : (m : ℤ) < S.n)
    (hcrit : ((m : ℤ) : WithTop ℤ) < simpleCriticalDepth S.chain S.b)
    {θ : simpleHGroup S.chain S.n S.b q.tail (m + 1) →* ℂˣ}
    (hθ : θ ∈ simpleCharacters ψF S.chain S.n S.b q.tail m) :
    simpleCharacterIntertwiningFactor S q m ⊆ characterNormalizer θ := by
  intro y hy
  rw [(hint F V ψF hψ S h0 hs q m hmn hcrit θ hθ).2]
  exact Set.mem_mul.mpr ⟨y, hy, 1, (relativeOrderNormalizer S.chain S.b).one_mem, mul_one y⟩

/-- Every centralizer unit intertwines every simple character. -/
theorem centralizerUnitGroup_subset_selfIntertwining
    (hint : SimpleCharacterIntertwiningStatement.{u, v})
    (ψF : AddChar F ℂ) (hψ : IsBKAdditiveCharacter ψF)
    (S : Stratum 𝒪[F] F V) (h0 : S.r = 0) (hs : S.IsSimple) (q : S.DefiningSequenceChoice)
    (m : ℕ) (hmn : (m : ℤ) < S.n)
    (hcrit : ((m : ℤ) : WithTop ℤ) < simpleCriticalDepth S.chain S.b)
    {θ : simpleHGroup S.chain S.n S.b q.tail (m + 1) →* ℂˣ}
    (hθ : θ ∈ simpleCharacters ψF S.chain S.n S.b q.tail m) :
    (centralizerUnitGroup S.b : Set G) ⊆ characterSelfIntertwining θ := by
  intro t ht
  rw [(hint F V ψF hψ S h0 hs q m hmn hcrit θ hθ).1]
  exact Set.mem_mul.mpr ⟨1 * t, Set.mem_mul.mpr ⟨1, simpleCharacterIntertwiningFactor_one_mem S q m,
    t, ht, rfl⟩, 1, simpleCharacterIntertwiningFactor_one_mem S q m, by simp⟩

/-- **High depth.** If `⌊n/2⌋ ≤ i` and the simple strata `[𝔄,n,i+1,β₁]`, `[𝔄,n,i+1,β₂]` on the
same chain have equal sets of pairs at depth `i+1`, then the strata are equivalent. -/
theorem simpleStratum_equivalent_of_pairs_eq_of_half_le
    (hrestriction : SimpleCharacterRestrictionStatement.{u, v})
    (hchoice : SimpleCharacterChoiceStatement.{u, v})
    (ψF : AddChar F ℂ) (hψ : IsBKAdditiveCharacter ψF) (L : LatticeChain 𝒪[F] F V) (n : ℤ)
    (i : ℕ) (S T : SimpleStratumAt L n ((i + 1 : ℕ) : ℤ)) (hi : n / 2 ≤ (i : ℤ))
    (h : simpleCharacterPairs ψF S.1 (i + 1) = simpleCharacterPairs ψF T.1 (i + 1))
    (q : S.1.DefiningSequenceChoice) (q' : T.1.DefiningSequenceChoice) :
    T.1.Equivalent S.1 := by
  obtain ⟨hLS, hnS, hrS, hsS⟩ := S.2
  obtain ⟨hLT, hnT, hrT, hsT⟩ := T.2
  have hr0S : 0 ≤ S.1.r := by rw [hrS]; positivity
  have hr0T : 0 ≤ T.1.r := by rw [hrT]; positivity
  have hkS : ((i + 1 : ℕ) : ℤ) < S.1.n := by have := S.1.r_lt_n; omega
  have hkT : ((i + 1 : ℕ) : ℤ) < T.1.n := by have := T.1.r_lt_n; omega
  obtain ⟨hH, hC, θ₀, hθ₀⟩ := simpleCharacters_correspond_of_pairs_eq hrestriction hchoice ψF hψ
    hsS hsT hr0S hr0T q q' (i + 1) hkS hkT h
  obtain ⟨φ₀, hφ₀, hag⟩ := hC.1 θ₀ hθ₀
  have hS' := simpleCharacterHighIndex.{u, v} F V ψF hψ S.1 q (i + 1) (by push_cast; omega)
  have hT' := simpleCharacterHighIndex.{u, v} F V ψF hψ T.1 q' (i + 1) (by push_cast; omega)
  -- the two element characters agree on `U^{i+2}`
  have key : ∀ g ∈ L.unitFiltration (i + 1 + 1),
      elementCharacter (traceCharacter ψF) (T.1.b - S.1.b) g = 1 := by
    intro g hg
    have hgS : g ∈ simpleHGroup S.1.chain S.1.n S.1.b q.tail (i + 1 + 1) := by
      rw [hS'.1, hLS]; exact hg
    obtain ⟨h₁, h₂, e⟩ := hag ⟨g, hgS⟩
    have v₁ := hS'.2 θ₀ hθ₀ ⟨g, h₁⟩
    have v₂ := hT'.2 φ₀ hφ₀ ⟨g, h₂⟩
    rw [mul_one, v₁, v₂] at e
    have e₀ : elementCharacter (traceCharacter ψF) S.1.b g =
        elementCharacter (traceCharacter ψF) T.1.b g := e
    have hsplit : T.1.b = S.1.b + (T.1.b - S.1.b) := by abel
    rw [hsplit, elementCharacter_add] at e₀
    have hne := elementCharacter_ne_zero ψF S.1.b g
    have e' : elementCharacter (traceCharacter ψF) S.1.b g * 1 =
        elementCharacter (traceCharacter ψF) S.1.b g *
          elementCharacter (traceCharacter ψF) (S.1.b + (T.1.b - S.1.b) - S.1.b) g := by
      rw [mul_one, add_sub_cancel_left]; exact e₀
    rw [add_sub_cancel_left] at e'
    exact (mul_left_cancel₀ hne e').symm
  -- additive duality on `U^{i+2}`
  have hn0 : 0 ≤ n := by have := S.1.r_lt_n; omega
  set N := n.toNat with hN
  have hNn : (N : ℤ) = n := Int.toNat_of_nonneg hn0
  have hbS : S.1.b ∈ L.endFiltration (-(N : ℤ)) := by
    have h := PureApproximation.mem_endFiltration_of_le_valuation S.1.chain (k := -S.1.n)
      (by exact_mod_cast S.1.valuation_ge)
    rw [hLS, hnS] at h
    rw [show (-(N : ℤ)) = -n by rw [hNn]]
    exact h
  have hbT : T.1.b ∈ L.endFiltration (-(N : ℤ)) := by
    have h := PureApproximation.mem_endFiltration_of_le_valuation T.1.chain (k := -T.1.n)
      (by exact_mod_cast T.1.valuation_ge)
    rw [hLT, hnT] at h
    rw [show (-(N : ℤ)) = -n by rw [hNn]]
    exact h
  have hdual := ((additiveDuality.{u, v} F V L ψF hψ.1 hψ.2).2 N (i + 1)
    (by omega) (by omega)).2.1 (T.1.b - S.1.b) (sub_mem hbT hbS)
  have hdiff : T.1.b - S.1.b ∈ L.endFiltration (-((i + 1 : ℕ) : ℤ)) := hdual.mp key
  unfold Stratum.Equivalent Stratum.coset
  rw [hLS, hLT, hrS, hrT]
  ext x
  simp only [Set.mem_ofPred_eq]
  constructor
  · intro hx
    have := add_mem hx hdiff
    rwa [show x - T.1.b + (T.1.b - S.1.b) = x - S.1.b by abel] at this
  · intro hx
    have := sub_mem hx hdiff
    rwa [show x - S.1.b - (T.1.b - S.1.b) = x - T.1.b by abel] at this

/-- **Low depth.** Let `[𝔄,n,i+1,β₁]` and `[𝔄,n,i+1,β₂]` be simple strata on the same chain with
equal sets of pairs at depth `i+1`, and suppose `2(i+1) ≤ r`, where `r = finiteCriticalDepth L n β₁`
is `−k₀(β₁,𝔄)` when `β₁` is not scalar and `n` when `β₁` is scalar. Then the sets of pairs at
depth `i` are equal as well. -/
theorem simpleCharacterPairs_pred_eq_of_two_mul_le
    (hgroups : SimpleStratumGroupPropertiesStatement.{u, v})
    (hrestriction : SimpleCharacterRestrictionStatement.{u, v})
    (hchoice : SimpleCharacterChoiceStatement.{u, v})
    (hint : SimpleCharacterIntertwiningStatement.{u, v})
    (hpair : SimpleCharacterPairingStatement.{u, v})
    (hcoh : SimpleCharacterCoherenceStatement.{u, v})
    (hdet : SimpleCharacterCentralizerDeterminantStatement.{u, v})
    (hinv : SimpleCharacterInvariantsStatement.{u, v})
    (ψF : AddChar F ℂ) (hψ : IsBKAdditiveCharacter ψF) (L : LatticeChain 𝒪[F] F V) (n : ℤ)
    (i : ℕ) (S T : SimpleStratumAt L n ((i + 1 : ℕ) : ℤ))
    (hr : 2 * ((i + 1 : ℕ) : ℤ) ≤ finiteCriticalDepth L n S.1.b)
    (h : simpleCharacterPairs ψF S.1 (i + 1) = simpleCharacterPairs ψF T.1 (i + 1))
    (q : S.1.DefiningSequenceChoice) (q' : T.1.DefiningSequenceChoice) :
    simpleCharacterPairs ψF S.1 i = simpleCharacterPairs ψF T.1 i := by
  have := L.finiteDimensional
  obtain ⟨hLS, hnS, hrS, hsS⟩ := S.2
  obtain ⟨hLT, hnT, hrT, hsT⟩ := T.2
  have hr0S : 0 ≤ S.1.r := by rw [hrS]; positivity
  have hr0T : 0 ≤ T.1.r := by rw [hrT]; positivity
  have hkS : ((i + 1 : ℕ) : ℤ) < S.1.n := by have := S.1.r_lt_n; omega
  have hkT : ((i + 1 : ℕ) : ℤ) < T.1.n := by have := T.1.r_lt_n; omega
  have hiS : (i : ℤ) < S.1.n := by push_cast at hkS; omega
  have hiT : (i : ℤ) < T.1.n := by push_cast at hkT; omega
  have hrS' : 2 * ((i + 1 : ℕ) : ℤ) ≤ finiteCriticalDepth S.1.chain S.1.n S.1.b := by
    rw [hLS, hnS]; exact hr
  -- a common character at depth `i + 1`
  obtain ⟨hH, hC, θ₀, hθ₀⟩ := simpleCharacters_correspond_of_pairs_eq hrestriction hchoice ψF hψ
    hsS hsT hr0S hr0T q q' (i + 1) hkS hkT h
  obtain ⟨φ₀, hφ₀, hag⟩ := hC.1 θ₀ hθ₀
  -- equal critical exponents
  have hcommon : (simpleCharacterPairs ψF S.1 (i + 1) ∩
      simpleCharacterPairs ψF T.1 (i + 1)).Nonempty := by
    rw [← h, Set.inter_self, simpleCharacterPairs_eq_image hchoice ψF hψ hsS hr0S q (i + 1) hkS]
    exact ⟨_, θ₀, hθ₀, rfl⟩
  have hcritEq := (hinv F V ψF hψ L n (i + 1) S T hcommon).1
  have hrT' : 2 * ((i + 1 : ℕ) : ℤ) ≤ finiteCriticalDepth T.1.chain T.1.n T.1.b := by
    have e : finiteCriticalDepth L n T.1.b = finiteCriticalDepth L n S.1.b := by
      simp only [finiteCriticalDepth, simpleCriticalDepth, hcritEq]
    rw [hLT, hnT, e]; exact hr
  -- extend the common character one step down
  obtain ⟨θ, hθ, hθres⟩ : ∃ θ ∈ simpleCharacters ψF S.1.chain S.1.n S.1.b q.tail i,
      θ.comp (Subgroup.inclusion (simpleHGroup_antitone S.1.chain S.1.n S.1.b q.tail
        (Nat.le_succ (i + 1)))) = θ₀ := by
    rw [← simpleCharacters_restriction_image hrestriction ψF hψ hsS hr0S q i hkS] at hθ₀
    exact hθ₀
  obtain ⟨φ, hφ, hφres⟩ : ∃ φ ∈ simpleCharacters ψF T.1.chain T.1.n T.1.b q'.tail i,
      φ.comp (Subgroup.inclusion (simpleHGroup_antitone T.1.chain T.1.n T.1.b q'.tail
        (Nat.le_succ (i + 1)))) = φ₀ := by
    rw [← simpleCharacters_restriction_image hrestriction ψF hψ hsT hr0T q' i hkT] at hφ₀
    exact hφ₀
  -- the first assertion of (3.5.9)
  have hHm : simpleHGroup S.1.chain S.1.n S.1.b q.tail (i + 1) =
      simpleHGroup T.1.chain T.1.n T.1.b q'.tail (i + 1) := by
    have h₁ := simpleHGroup_eq_of_simpleCharacterPairs_eq hgroups hrestriction hchoice hint hpair
      ψF hψ L n i S T h q q'
    rw [hLS, hnS, hLT, hnT]
    exact h₁
  -- depth-zero presentations
  have hs₀ := Stratum.isSimple_atDepthZero hsS hr0S
  have ht₀ := Stratum.isSimple_atDepthZero hsT hr0T
  have hcS : ∀ k : ℕ, k ≤ i + 1 → ((k : ℤ) : WithTop ℤ) < simpleCriticalDepth S.1.chain S.1.b :=
    fun k hk => lt_simpleCriticalDepth_of_lt _ S.1.n _ (by push_cast at hrS'; omega)
  have hcT : ∀ k : ℕ, k ≤ i + 1 → ((k : ℤ) : WithTop ℤ) < simpleCriticalDepth T.1.chain T.1.b :=
    fun k hk => lt_simpleCriticalDepth_of_lt _ T.1.n _ (by push_cast at hrT'; omega)
  -- the quotient of the two lifts
  let φS := φ.comp (Subgroup.inclusion hHm.le)
  let χ := φS / θ
  have hBθ := centralizerUnitGroup_subset_selfIntertwining hint ψF hψ
    (S.1.atDepthZero (hr0S.trans_lt S.1.r_lt_n)) rfl hs₀ (q.atDepthZero hr0S) i hiS
    (hcS i (Nat.le_succ i)) hθ
  have hBθ₀ := centralizerUnitGroup_subset_selfIntertwining hint ψF hψ
    (S.1.atDepthZero (hr0S.trans_lt S.1.r_lt_n)) rfl hs₀ (q.atDepthZero hr0S) (i + 1) hkS
    (hcS (i + 1) le_rfl) hθ₀
  have hBφ := centralizerUnitGroup_subset_selfIntertwining hint ψF hψ
    (T.1.atDepthZero (hr0T.trans_lt T.1.r_lt_n)) rfl ht₀ (q'.atDepthZero hr0T) i hiT
    (hcT i (Nat.le_succ i)) hφ
  have hI₀ : characterSelfIntertwining θ₀ = characterSelfIntertwining φ₀ :=
    characterSelfIntertwining_eq_of_agree hH θ₀ φ₀ hag
  have hIφ₀ := (hint F V ψF hψ (T.1.atDepthZero (hr0T.trans_lt T.1.r_lt_n)) rfl ht₀
    (q'.atDepthZero hr0T) (i + 1) hkT (hcT (i + 1) le_rfl) φ₀ hφ₀).1
  have hYsub := simpleCharacterIntertwiningFactor_succ_subset
    (T.1.atDepthZero (hr0T.trans_lt T.1.r_lt_n)) (q'.atDepthZero hr0T) i hrT'
  have hYN := simpleCharacterIntertwiningFactor_subset_normalizer hint ψF hψ
    (T.1.atDepthZero (hr0T.trans_lt T.1.r_lt_n)) rfl ht₀ (q'.atDepthZero hr0T) i hiT
    (hcT i (Nat.le_succ i)) hφ
  have hBχ : (centralizerUnitGroup S.1.b : Set G) ⊆ characterSelfIntertwining χ := by
    intro t ht
    have ht₀ : t ∈ characterSelfIntertwining φ₀ := hI₀ ▸ hBθ₀ ht
    have ht₁ := (Set.ext_iff.mp hIφ₀ t).mp ht₀
    obtain ⟨a, ha, y₂, hy₂, rfl⟩ := Set.mem_mul.mp ht₁
    obtain ⟨y₁, hy₁, s, hs, rfl⟩ := Set.mem_mul.mp ha
    have htφ : y₁ * s * y₂ ∈ characterSelfIntertwining φ :=
      mul_mul_mem_characterSelfIntertwining (hYN (hYsub hy₁)) (hBφ hs) (hYN (hYsub hy₂))
    have htφS : y₁ * s * y₂ ∈ characterSelfIntertwining φS := by
      rw [characterSelfIntertwining_comp_inclusion hHm φ]; exact htφ
    exact mem_characterSelfIntertwining_div_of_mem htφS (hBθ ht)
  have hχdet : factorsThroughCentralizerDet S.1.b χ := hdet F V S.1 q hsS i χ hBχ
  have hχtriv : ∀ g : simpleHGroup S.1.chain S.1.n S.1.b q.tail (i + 1),
      (g : G) ∈ simpleHGroup S.1.chain S.1.n S.1.b q.tail (i + 1 + 1) → χ g = 1 := by
    intro g hg
    obtain ⟨h₁, h₂, e⟩ := hag ⟨g, hg⟩
    have eθ : θ g = θ₀ ⟨g, h₁⟩ := by rw [← hθres]; rfl
    have eφ : φS g = φ₀ ⟨g, h₂⟩ := by rw [← hφres]; rfl
    have hval : θ g = φS g := by
      rw [eθ, eφ]
      exact Units.ext (by rw [e, mul_one])
    change φS g / θ g = 1
    rw [hval, div_self']
  have hφSmem : φS ∈ simpleCharacters ψF S.1.chain S.1.n S.1.b q.tail i := by
    have hmul := simpleCharacter_mul_mem_of_belowCutoff hrestriction ψF hψ q hsS hr0S i hiS
      (by push_cast at hrS'; omega) hθ hχdet hχtriv
    have e : θ * χ = φS := by
      ext g
      simp only [χ, MonoidHom.mul_apply, MonoidHom.div_apply, mul_div_cancel]
    rwa [e] at hmul
  -- coherence at depth `i`
  have hiS' : (i : ℤ) ≤ S.1.r := by rw [hrS]; push_cast; omega
  have hiT' : (i : ℤ) ≤ T.1.r := by rw [hrT]; push_cast; omega
  have hcohres := hcoh F V ψF hψ (S.1.lowerIndex i hiS') (T.1.lowerIndex i hiT') i
    (by change T.1.chain.order = S.1.chain.order; rw [hLT, hLS])
    (by change T.1.n = S.1.n; rw [hnT, hnS]) rfl rfl (hsS.lowerIndex hiS') (hsT.lowerIndex hiT')
    (q.atIndex hiS') (q'.atIndex hiT') hHm (characterSet_ndrec_inter_nonempty hHm hφ hφSmem)
  have hcorr := characterSetTwistCorrespondence_of_ndrec_eq hHm hcohres
  rw [simpleCharacterPairs_eq_image hchoice ψF hψ hsS hr0S q i hiS,
    simpleCharacterPairs_eq_image hchoice ψF hψ hsT hr0T q' i hiT]
  exact (characterPair_image_eq_iff _ _ ⟨θ, hθ⟩).mpr ⟨hHm, hcorr⟩

omit [TopologicalSpace F] [IsNonarchimedeanLocalField F] in
/-- A stratum without defining sequences has no simple character pairs. -/
theorem simpleCharacterPairs_eq_empty {S : Stratum 𝒪[F] F V}
    (h : IsEmpty S.DefiningSequenceChoice) (ψF : AddChar F ℂ) (k : ℕ) :
    simpleCharacterPairs ψF S k = ∅ := by
  simp [simpleCharacterPairs]

/-- **The second assertion of BK93 (3.5.9) at high and at low depth.** Assume the published
statements listed. Let `[𝔄,n,m,β₁]`, `[𝔄,n,m,β₂]` be simple strata on the same chain with
`m ≥ 1` and equal sets of simple character pairs at depth `m`. If `⌊n/2⌋ ≤ m − 1` or
`2m ≤ finiteCriticalDepth L n β₁` (this is `−k₀(β₁,𝔄)` when `β₁` is not scalar and `n` when `β₁`
is scalar), there is a simple stratum `[𝔄,n,m,β₁']` equivalent to `[𝔄,n,m,β₁]` with the same
sets of pairs at depth `m − 1` as `[𝔄,n,m,β₂]`. -/
def SimpleCharacterLoweringOuterCasesReductionStatement : Prop :=
  SimpleStratumGroupPropertiesStatement.{uF, uV} → SimpleCharacterRestrictionStatement.{uF, uV} →
    SimpleCharacterChoiceStatement.{uF, uV} → SimpleCharacterIntertwiningStatement.{uF, uV} →
    SimpleCharacterPairingStatement.{uF, uV} → SimpleCharacterCoherenceStatement.{uF, uV} →
    SimpleCharacterCentralizerDeterminantStatement.{uF, uV} →
    SimpleCharacterInvariantsStatement.{uF, uV} →
    ∀ (F : Type uF) [Field F] [ValuativeRel F] [TopologicalSpace F]
      [IsNonarchimedeanLocalField F] (V : Type uV) [AddCommGroup V] [Module F V]
      (ψF : AddChar F ℂ), IsBKAdditiveCharacter ψF →
      ∀ (L : LatticeChain 𝒪[F] F V) (n : ℤ) (m : ℕ), 1 ≤ m →
      ∀ (S T : SimpleStratumAt L n m),
        simpleCharacterPairs ψF S.1 m = simpleCharacterPairs ψF T.1 m →
        (n / 2 ≤ ((m - 1 : ℕ) : ℤ) ∨ 2 * (m : ℤ) ≤ finiteCriticalDepth L n S.1.b) →
        ∃ S' : SimpleStratumAt L n m, S'.1.Equivalent S.1 ∧
          simpleCharacterPairs ψF S'.1 (m - 1) = simpleCharacterPairs ψF T.1 (m - 1)

theorem simpleCharacterLoweringOuterCasesReduction :
    SimpleCharacterLoweringOuterCasesReductionStatement.{uF, uV} := by
  intro hgroups hrestriction hchoice hint hpair hcoh hdet hinv F _ _ _ _ V _ _ ψF hψ L n m hm
    S T h hcase
  obtain ⟨i, rfl⟩ : ∃ i, m = i + 1 := ⟨m - 1, by omega⟩
  simp only [Nat.add_sub_cancel] at hcase ⊢
  by_cases hq : Nonempty S.1.DefiningSequenceChoice
  · obtain ⟨q⟩ := hq
    have hq' : Nonempty T.1.DefiningSequenceChoice := by
      by_contra hT
      have hr0S : 0 ≤ S.1.r := by rw [S.2.2.2.1]; positivity
      have hkS : ((i + 1 : ℕ) : ℤ) < S.1.n := by have := S.1.r_lt_n; rw [S.2.2.2.1] at this; exact this
      have hne := (hrestriction F V ψF hψ (S.1.atDepthZero (hr0S.trans_lt S.1.r_lt_n)) rfl
        (Stratum.isSimple_atDepthZero S.2.2.2.2 hr0S) (q.atDepthZero hr0S)).2.2.2.2 (i + 1) hkS
      rw [simpleCharacterPairs_eq_empty (not_nonempty_iff.mp hT),
        simpleCharacterPairs_eq_image hchoice ψF hψ S.2.2.2.2 hr0S q (i + 1) hkS] at h
      have he := Set.image_eq_empty.mp h
      have hne' : (simpleCharacters ψF S.1.chain S.1.n S.1.b q.tail (i + 1)).Nonempty := hne
      rw [he] at hne'
      exact Set.not_nonempty_empty hne'
    obtain ⟨q'⟩ := hq'
    rcases hcase with hhigh | hlow
    · exact ⟨T, simpleStratum_equivalent_of_pairs_eq_of_half_le hrestriction hchoice ψF hψ L n i
        S T hhigh h q q', rfl⟩
    · exact ⟨S, rfl,
        simpleCharacterPairs_pred_eq_of_two_mul_le hgroups hrestriction hchoice hint hpair hcoh hdet
          hinv ψF hψ L n i S T (by exact_mod_cast hlow) h q q'⟩
  · refine ⟨S, rfl, ?_⟩
    have hS : IsEmpty S.1.DefiningSequenceChoice := not_nonempty_iff.mp hq
    have hT : IsEmpty T.1.DefiningSequenceChoice := by
      by_contra hT
      obtain ⟨q'⟩ := not_isEmpty_iff.mp hT
      have hr0T : 0 ≤ T.1.r := by rw [T.2.2.2.1]; positivity
      have hkT : ((i + 1 : ℕ) : ℤ) < T.1.n := by have := T.1.r_lt_n; rw [T.2.2.2.1] at this; exact this
      have hne := (hrestriction F V ψF hψ (T.1.atDepthZero (hr0T.trans_lt T.1.r_lt_n)) rfl
        (Stratum.isSimple_atDepthZero T.2.2.2.2 hr0T) (q'.atDepthZero hr0T)).2.2.2.2 (i + 1) hkT
      rw [simpleCharacterPairs_eq_empty hS,
        simpleCharacterPairs_eq_image hchoice ψF hψ T.2.2.2.2 hr0T q' (i + 1) hkT] at h
      have he := Set.image_eq_empty.mp h.symm
      have hne' : (simpleCharacters ψF T.1.chain T.1.n T.1.b q'.tail (i + 1)).Nonempty := hne
      rw [he] at hne'
      exact Set.not_nonempty_empty hne'
    rw [simpleCharacterPairs_eq_empty hS, simpleCharacterPairs_eq_empty hT]

end Langlands.BushnellKutzko
