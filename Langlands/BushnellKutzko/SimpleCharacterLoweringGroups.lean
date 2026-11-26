import Langlands.BushnellKutzko.SimpleCharacterLoweringLattice
import Langlands.BushnellKutzko.SimpleCharacterCoreFibre
import Langlands.BushnellKutzko.SimpleCharacterPairingStatement
import Langlands.BushnellKutzko.SimpleStratumLatticePropertiesProof
import Langlands.BushnellKutzko.SimpleCharacterCovarianceStatement
import Langlands.BushnellKutzko.SimpleCharacterChoiceStatement
import Langlands.BushnellKutzko.SimpleCharacterPairs

/-! # The groups `H^m` of simple strata with a common simple character -/

noncomputable section

open ValuativeRel
open scoped commutatorElement

namespace Langlands.BushnellKutzko

universe u v uF uV

variable {F : Type u} [Field F] [ValuativeRel F] [TopologicalSpace F]
  [IsNonarchimedeanLocalField F] {V : Type v} [AddCommGroup V] [Module F V]

local notation "A" => Module.End F V
local notation "G" => (Module.End F V)ˣ

/-- `ψ_d` is trivial at `h` when `d ∈ 𝔓^j`, `h − 1 ∈ 𝔓^k` and `j + k ≥ 1`. -/
theorem elementCharacter_eq_one_of_mem_endFiltration (ψF : AddChar F ℂ) (hψ : IsBKAdditiveCharacter ψF)
    (L : LatticeChain 𝒪[F] F V) {j k : ℤ} (hjk : 1 ≤ j + k) {d : A}
    (hd : d ∈ L.endFiltration j) {h : G} (hh : (h : A) - 1 ∈ L.endFiltration k) :
    elementCharacter (traceCharacter ψF) d h = 1 := by
  have hdual := (additiveDuality F V L ψF hψ.1 hψ.2).1 k
  have ha : d ∈ additiveDual (traceCharacter ψF) (L.endFiltration k : Set A) := by
    rw [hdual]
    exact L.endFiltration_antitone (by omega) hd
  exact ha _ hh

/-- Conjugation by `g ∈ U^a(𝔄)` does not change `ψ_c` at `h` when `c ∈ 𝔓^j`,
`h − 1 ∈ 𝔓^b` and `j + a + b ≥ 1`. -/
theorem elementCharacter_conj_eq_of_mem (ψF : AddChar F ℂ) (hψ : IsBKAdditiveCharacter ψF)
    (L : LatticeChain 𝒪[F] F V) {j b : ℤ} {a : ℕ} (hjab : 1 ≤ j + a + b) {c : A}
    (hc : c ∈ L.endFiltration j) {g : G} (hg : g ∈ L.unitFiltration a) {h : G}
    (hh : (h : A) - 1 ∈ L.endFiltration b) :
    elementCharacter (traceCharacter ψF) c (g * h * g⁻¹) =
      elementCharacter (traceCharacter ψF) c h := by
  rw [elementCharacter_conj]
  have hsplit : (↑g⁻¹ : A) * c * (g : A) = c + ((↑g⁻¹ : A) * c * (g : A) - c) := by abel
  rw [hsplit, elementCharacter_add]
  have hd : (↑g⁻¹ : A) * c * (g : A) - c ∈ L.endFiltration (j + a) := by
    have he : (↑g⁻¹ : A) * c * (g : A) - c =
        (↑g⁻¹ : A) * (c * ((g : A) - 1) - ((g : A) - 1) * c) := by
      calc (↑g⁻¹ : A) * c * (g : A) - c = (↑g⁻¹ : A) * c * (g : A) - ((↑g⁻¹ : A) * g) * c := by
            rw [Units.inv_mul, one_mul]
        _ = (↑g⁻¹ : A) * (c * ((g : A) - 1) - ((g : A) - 1) * c) := by noncomm_ring
    rw [he]
    have hinv : (↑g⁻¹ : A) ∈ L.endFiltration 0 :=
      (L.mem_order_iff_mem_endFiltration).1 hg.2.1
    have h1 : c * ((g : A) - 1) ∈ L.endFiltration (j + a) := L.mul_mem_endFiltration hc hg.2.2
    have h2 : ((g : A) - 1) * c ∈ L.endFiltration (j + a) := by
      have := L.mul_mem_endFiltration hg.2.2 hc
      rwa [add_comm] at this
    simpa using L.mul_mem_endFiltration hinv (sub_mem h1 h2)
  rw [elementCharacter_eq_one_of_mem_endFiltration ψF hψ L (by omega) hd hh, mul_one]

/-- The commutator pairing of `SimpleCharacterPairingStatement` identifies `H^{i+1}` inside
`J^{i+1}`: an element of `J^{i+1}` lies in `H^{i+1}` exactly when `θ` is trivial on its
commutators with all of `J^{i+1}`. -/
theorem mem_simpleHGroup_iff_commutator (hpair : SimpleCharacterPairingStatement.{u, v})
    (ψF : AddChar F ℂ) (hψ : IsBKAdditiveCharacter ψF)
    (S : Stratum 𝒪[F] F V) (h0 : S.r = 0) (hs : S.IsSimple) (q : S.DefiningSequenceChoice)
    (i : ℕ) (hin : ((i + 1 : ℕ) : ℤ) ≤ S.n)
    (hcrit : (((i + 1 : ℕ) : ℤ) : WithTop ℤ) ≤ simpleCriticalDepth S.chain S.b)
    (θ : simpleHGroup S.chain S.n S.b q.tail (i + 1) →* ℂˣ)
    (hθ : θ ∈ simpleCharacters ψF S.chain S.n S.b q.tail i) :
    simpleHGroup S.chain S.n S.b q.tail (i + 1) ≤ simpleJGroup S.chain S.n S.b q.tail (i + 1) ∧
    ∀ x ∈ simpleJGroup S.chain S.n S.b q.tail (i + 1),
      (x ∈ simpleHGroup S.chain S.n S.b q.tail (i + 1) ↔
        ∀ y ∈ simpleJGroup S.chain S.n S.b q.tail (i + 1),
          ∀ hc : ⁅x, y⁆ ∈ simpleHGroup S.chain S.n S.b q.tail (i + 1), θ ⟨_, hc⟩ = 1) := by
  have h := hpair F V ψF hψ S h0 hs q i hin hcrit θ hθ
  set H := simpleHGroup S.chain S.n S.b q.tail (i + 1)
  set J := simpleJGroup S.chain S.n S.b q.tail (i + 1)
  obtain ⟨hHJ, hN, hrest⟩ := h
  let := hN
  obtain ⟨B, hB, -, hnd⟩ := hrest
  refine ⟨hHJ, fun x hx => ⟨fun hxH y hy hc => ?_, fun hall => ?_⟩⟩
  · obtain ⟨hc', he⟩ := hB ⟨x, hx⟩ ⟨y, hy⟩
    have h1 : QuotientGroup.mk' (H.comap J.subtype) ⟨x, hx⟩ = 1 :=
      (QuotientGroup.eq_one_iff (⟨x, hx⟩ : J)).mpr hxH
    rw [h1, map_one, MonoidHom.one_apply] at he
    exact he.symm
  · have hq : QuotientGroup.mk' (H.comap J.subtype) ⟨x, hx⟩ = 1 := by
      apply hnd
      intro y'
      obtain ⟨⟨y, hy⟩, rfl⟩ := QuotientGroup.mk'_surjective _ y'
      obtain ⟨hc', he⟩ := hB ⟨x, hx⟩ ⟨y, hy⟩
      rw [he]
      exact hall y hy hc'
    exact (QuotientGroup.eq_one_iff (⟨x, hx⟩ : J)).mp hq

/-- The adjacent restriction clause of `SimpleCharacterRestrictionStatement` for a simple
stratum at a nonnegative index: restriction maps `C(𝔄,i,β)` onto `C(𝔄,i+1,β)`. -/
theorem simpleCharacters_restriction_image (hrestriction : SimpleCharacterRestrictionStatement.{u, v})
    (ψF : AddChar F ℂ) (hψ : IsBKAdditiveCharacter ψF)
    {S : Stratum 𝒪[F] F V} (hs : S.IsSimple) (hr : 0 ≤ S.r) (q : S.DefiningSequenceChoice)
    (i : ℕ) (hin : (i : ℤ) + 1 < S.n) :
    (fun χ : simpleHGroup S.chain S.n S.b q.tail (i + 1) →* ℂˣ =>
        χ.comp (Subgroup.inclusion (simpleHGroup_antitone S.chain S.n S.b q.tail
          (Nat.le_succ (i + 1))))) ''
      simpleCharacters ψF S.chain S.n S.b q.tail i =
      simpleCharacters ψF S.chain S.n S.b q.tail (i + 1) := by
  have h := hrestriction F V ψF hψ (S.atDepthZero (hr.trans_lt S.r_lt_n)) rfl
    (Stratum.isSimple_atDepthZero hs hr) (q.atDepthZero hr)
  exact h.2.2.2.1 i hin

omit [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F] in
/-- The functions `ψ_b` take nonzero values. -/
theorem elementCharacter_ne_zero (ψF : AddChar F ℂ) (b : A) (g : G) :
    elementCharacter (traceCharacter ψF) b g ≠ 0 := by
  intro h0
  have h := AddChar.map_add_eq_mul (traceCharacter (V := V) ψF) (b * ((g : A) - 1))
    (-(b * ((g : A) - 1)))
  rw [add_neg_cancel, AddChar.map_zero_eq_one] at h
  rw [elementCharacter_apply] at h0
  rw [h0, zero_mul] at h
  exact one_ne_zero h

/-- If two characters on equal subgroups differ by functions that are invariant under
conjugation by `g`, then `g` intertwining the first character intertwines the second. -/
theorem mem_characterSelfIntertwining_of_relation {K : Type*} [Group K] {H₁ H₂ : Subgroup K}
    (hH : H₁ = H₂) (χ₁ : H₁ →* ℂˣ) (χ₂ : H₂ →* ℂˣ) (f₁ f₂ : K → ℂ)
    (hf₂ : ∀ x ∈ H₂, f₂ x ≠ 0)
    (hrel : ∀ (x : K) (h₁ : x ∈ H₁) (h₂ : x ∈ H₂),
      (χ₁ ⟨x, h₁⟩ : ℂ) * f₁ x = (χ₂ ⟨x, h₂⟩ : ℂ) * f₂ x)
    {g : K} (hinv : ∀ h ∈ H₂, g * h * g⁻¹ ∈ H₂ →
      f₁ (g * h * g⁻¹) = f₁ h ∧ f₂ (g * h * g⁻¹) = f₂ h)
    (hg : g ∈ characterSelfIntertwining χ₁) : g ∈ characterSelfIntertwining χ₂ := by
  intro h hh
  have h₁ : (h : K) ∈ H₁ := hH ▸ h.2
  have hh₁ : g * (h : K) * g⁻¹ ∈ H₁ := hH ▸ hh
  have e1 := hrel _ hh₁ hh
  have e2 := hrel _ h₁ h.2
  have hgi : χ₁ ⟨_, hh₁⟩ = χ₁ ⟨h, h₁⟩ := hg ⟨h, h₁⟩ hh₁
  obtain ⟨i1, i2⟩ := hinv h h.2 hh
  apply Units.ext
  apply mul_right_cancel₀ (hf₂ h h.2)
  calc (χ₂ ⟨_, hh⟩ : ℂ) * f₂ h = (χ₂ ⟨_, hh⟩ : ℂ) * f₂ (g * h * g⁻¹) := by rw [i2]
    _ = (χ₁ ⟨_, hh₁⟩ : ℂ) * f₁ (g * h * g⁻¹) := e1.symm
    _ = (χ₁ ⟨h, h₁⟩ : ℂ) * f₁ h := by rw [hgi, i1]
    _ = (χ₂ h : ℂ) * f₂ h := e2

/-- **Equal groups `H^{i+1}` below half the level.** Let `[𝔄,n,r,β₁]` and `[𝔄,n,r',β₂]` be
simple strata on the same chain with `0 ≤ r, r' ≤ 2i+1` and `i < ⌊n/2⌋`. If the groups
`H^{i+2}(β_j)` coincide and carry a common character of `C(𝔄,i+1,β₁)` and `C(𝔄,i+1,β₂)`,
then `H^{i+1}(β₁) = H^{i+1}(β₂)`. -/
theorem simpleHGroup_eq_of_common_character_of_lt_half
    (hgroups : SimpleStratumGroupPropertiesStatement.{u, v})
    (hrestriction : SimpleCharacterRestrictionStatement.{u, v})
    (hint : SimpleCharacterIntertwiningStatement.{u, v})
    (hpair : SimpleCharacterPairingStatement.{u, v})
    (ψF : AddChar F ℂ) (hψ : IsBKAdditiveCharacter ψF)
    (S T : Stratum 𝒪[F] F V) (hL : T.chain = S.chain) (hn : T.n = S.n)
    (hS : S.IsSimple) (hT : T.IsSimple) (i : ℕ)
    (hrS : 0 ≤ S.r) (hrS' : S.r ≤ 2 * (i : ℤ) + 1) (hrT : 0 ≤ T.r) (hrT' : T.r ≤ 2 * (i : ℤ) + 1)
    (hi : (i : ℤ) < S.n / 2)
    (q : S.DefiningSequenceChoice) (q' : T.DefiningSequenceChoice)
    (hH : simpleHGroup S.chain S.n S.b q.tail (i + 1 + 1) =
      simpleHGroup T.chain T.n T.b q'.tail (i + 1 + 1))
    (θ₀ : simpleHGroup S.chain S.n S.b q.tail (i + 1 + 1) →* ℂˣ)
    (hθ₀ : θ₀ ∈ simpleCharacters ψF S.chain S.n S.b q.tail (i + 1))
    (φ₀ : simpleHGroup T.chain T.n T.b q'.tail (i + 1 + 1) →* ℂˣ)
    (hφ₀ : φ₀ ∈ simpleCharacters ψF T.chain T.n T.b q'.tail (i + 1))
    (hagree : characterAgreesOn (simpleHGroup S.chain S.n S.b q.tail (i + 1 + 1)) θ₀ φ₀
      (fun _ => 1)) :
    simpleHGroup S.chain S.n S.b q.tail (i + 1) = simpleHGroup T.chain T.n T.b q'.tail (i + 1) := by
  have hin : (i : ℤ) + 1 < S.n := by omega
  have hinT : (i : ℤ) + 1 < T.n := by rw [hn]; exact hin
  have hiT : (i : ℤ) < T.n / 2 := by rw [hn]; exact hi
  -- extend the common character one step down
  obtain ⟨θ, hθ, hθres⟩ : ∃ θ ∈ simpleCharacters ψF S.chain S.n S.b q.tail i,
      θ.comp (Subgroup.inclusion (simpleHGroup_antitone S.chain S.n S.b q.tail
        (Nat.le_succ (i + 1)))) = θ₀ := by
    rw [← simpleCharacters_restriction_image hrestriction ψF hψ hS hrS q i hin] at hθ₀
    exact hθ₀
  obtain ⟨φ, hφ, hφres⟩ : ∃ φ ∈ simpleCharacters ψF T.chain T.n T.b q'.tail i,
      φ.comp (Subgroup.inclusion (simpleHGroup_antitone T.chain T.n T.b q'.tail
        (Nat.le_succ (i + 1)))) = φ₀ := by
    rw [← simpleCharacters_restriction_image hrestriction ψF hψ hT hrT q' i hinT] at hφ₀
    exact hφ₀
  -- core approximations at depth `i`
  obtain ⟨c₁, hc₁⟩ := exists_simpleCharacterCore_with_depth_bound
    simpleStratumLatticeProperties.{u, v} hrestriction ψF hψ q hS hrS i hi
  obtain ⟨c₂, hc₂⟩ := exists_simpleCharacterCore_with_depth_bound
    simpleStratumLatticeProperties.{u, v} hrestriction ψF hψ q' hT hrT i hiT
  have hr₁ : c₁.stratum.r ≤ 2 * (i : ℤ) + 1 := hc₁.trans (max_le hrS' le_rfl)
  have hr₂ : c₂.stratum.r ≤ 2 * (i : ℤ) + 1 := hc₂.trans (max_le hrT' le_rfl)
  have hr₁0 : 0 ≤ c₁.stratum.r := hrS.trans c₁.depth_le
  have hr₂0 : 0 ≤ c₂.stratum.r := hrT.trans c₂.depth_le
  obtain ⟨θ', hθ', hθθ'⟩ := c₁.twist.1 θ hθ
  obtain ⟨φ', hφ', hφφ'⟩ := c₂.twist.1 φ hφ
  have hs₁ := Stratum.isSimple_atDepthZero c₁.isSimple hr₁0
  have hs₂ := Stratum.isSimple_atDepthZero c₂.isSimple hr₂0
  have hcut₁ : 2 * ((i + 1 : ℕ) : ℤ) ≤
      finiteCriticalDepth c₁.stratum.chain c₁.stratum.n c₁.stratum.b := by
    have := c₁.below_cutoff; push_cast; omega
  have hcut₂ : 2 * ((i + 1 : ℕ) : ℤ) ≤
      finiteCriticalDepth c₂.stratum.chain c₂.stratum.n c₂.stratum.b := by
    have := c₂.below_cutoff; push_cast; omega
  have hcrit₁ : (((i + 1 : ℕ) : ℤ) : WithTop ℤ) ≤
      simpleCriticalDepth c₁.stratum.chain c₁.stratum.b := by
    cases hd : simpleCriticalDepth c₁.stratum.chain c₁.stratum.b with
    | top => exact le_top
    | coe d =>
      have hrd : finiteCriticalDepth c₁.stratum.chain c₁.stratum.n c₁.stratum.b = d := by
        simp [finiteCriticalDepth, hd]
      exact WithTop.coe_le_coe.mpr (by omega)
  have hcrit₂ : (((i + 1 : ℕ) : ℤ) : WithTop ℤ) ≤
      simpleCriticalDepth c₂.stratum.chain c₂.stratum.b := by
    cases hd : simpleCriticalDepth c₂.stratum.chain c₂.stratum.b with
    | top => exact le_top
    | coe d =>
      have hrd : finiteCriticalDepth c₂.stratum.chain c₂.stratum.n c₂.stratum.b = d := by
        simp [finiteCriticalDepth, hd]
      exact WithTop.coe_le_coe.mpr (by omega)
  have hn₁ : ((i + 1 : ℕ) : ℤ) < c₁.stratum.n := by rw [c₁.level_eq]; push_cast; omega
  have hn₂ : ((i + 1 : ℕ) : ℤ) < c₂.stratum.n := by rw [c₂.level_eq]; push_cast; omega
  -- the restrictions of the core characters
  set ι₁ := Subgroup.inclusion (simpleHGroup_antitone c₁.stratum.chain c₁.stratum.n c₁.stratum.b
    c₁.sequence.tail (Nat.le_succ (i + 1)))
  set ι₂ := Subgroup.inclusion (simpleHGroup_antitone c₂.stratum.chain c₂.stratum.n c₂.stratum.b
    c₂.sequence.tail (Nat.le_succ (i + 1)))
  have hθ'₀ : θ'.comp ι₁ ∈ simpleCharacters ψF c₁.stratum.chain c₁.stratum.n c₁.stratum.b
      c₁.sequence.tail (i + 1) := by
    rw [← simpleCharacters_restriction_image hrestriction ψF hψ c₁.isSimple hr₁0 c₁.sequence i
      (by rw [c₁.level_eq]; exact hin)]
    exact ⟨θ', hθ', rfl⟩
  have hφ'₀ : φ'.comp ι₂ ∈ simpleCharacters ψF c₂.stratum.chain c₂.stratum.n c₂.stratum.b
      c₂.sequence.tail (i + 1) := by
    rw [← simpleCharacters_restriction_image hrestriction ψF hψ c₂.isSimple hr₂0 c₂.sequence i
      (by rw [c₂.level_eq, hn]; exact hin)]
    exact ⟨φ', hφ', rfl⟩
  have hJ₁ := simpleJGroup_eq_selfIntertwining_inter hgroups hint ψF hψ
    (c₁.stratum.atDepthZero (hr₁0.trans_lt c₁.stratum.r_lt_n)) rfl hs₁
    (c₁.sequence.atDepthZero hr₁0) (i + 1) (by omega) hn₁ hcut₁ _ hθ'₀
  have hJ₂ := simpleJGroup_eq_selfIntertwining_inter hgroups hint ψF hψ
    (c₂.stratum.atDepthZero (hr₂0.trans_lt c₂.stratum.r_lt_n)) rfl hs₂
    (c₂.sequence.atDepthZero hr₂0) (i + 1) (by omega) hn₂ hcut₂ _ hφ'₀
  -- the domains one step deeper
  have hD₁ := SimpleCharacterCore.domain_eq_of_le hgroups hS hrS c₁ (Nat.le_succ i)
  have hD₂ := SimpleCharacterCore.domain_eq_of_le hgroups hT hrT c₂ (Nat.le_succ i)
  have hD : simpleHGroup c₁.stratum.chain c₁.stratum.n c₁.stratum.b c₁.sequence.tail (i + 1 + 1) =
      simpleHGroup c₂.stratum.chain c₂.stratum.n c₂.stratum.b c₂.sequence.tail (i + 1 + 1) :=
    hD₁.symm.trans (hH.trans hD₂)
  have hU₁ : c₁.stratum.chain = S.chain := c₁.chain_eq
  have hU₂ : c₂.stratum.chain = S.chain := c₂.chain_eq.trans hL
  -- the additive twists between the original and the core characters
  set f₁ := elementCharacter (traceCharacter ψF) (S.b - c₁.stratum.b)
  set f₂ := elementCharacter (traceCharacter ψF) (T.b - c₂.stratum.b)
  have he₁ : S.b - c₁.stratum.b ∈ S.chain.endFiltration (-(2 * (i : ℤ) + 1)) :=
    S.chain.endFiltration_antitone (by omega) c₁.congruence
  have he₂ : T.b - c₂.stratum.b ∈ S.chain.endFiltration (-(2 * (i : ℤ) + 1)) := by
    have h := c₂.congruence
    rw [hL] at h
    exact S.chain.endFiltration_antitone (by omega) h
  have key : ∀ (x : G)
      (h₁ : x ∈ simpleHGroup c₁.stratum.chain c₁.stratum.n c₁.stratum.b c₁.sequence.tail (i + 1))
      (h₂ : x ∈ simpleHGroup c₂.stratum.chain c₂.stratum.n c₂.stratum.b c₂.sequence.tail (i + 1)),
      x ∈ simpleHGroup S.chain S.n S.b q.tail (i + 1 + 1) →
      (θ' ⟨x, h₁⟩ : ℂ) * f₁ x = (φ' ⟨x, h₂⟩ : ℂ) * f₂ x := by
    intro x h₁ h₂ hx
    have hxS : x ∈ simpleHGroup S.chain S.n S.b q.tail (i + 1) :=
      simpleHGroup_antitone _ _ _ _ (Nat.le_succ (i + 1)) hx
    have hxT' : x ∈ simpleHGroup T.chain T.n T.b q'.tail (i + 1 + 1) := hH ▸ hx
    have hxT : x ∈ simpleHGroup T.chain T.n T.b q'.tail (i + 1) :=
      simpleHGroup_antitone _ _ _ _ (Nat.le_succ (i + 1)) hxT'
    obtain ⟨a₁, b₁, eθ⟩ := hθθ' ⟨x, hxS⟩
    obtain ⟨a₂, b₂, eφ⟩ := hφφ' ⟨x, hxT⟩
    obtain ⟨cθ, cφ, e₀⟩ := hagree ⟨x, hx⟩
    have r₁ : θ ⟨x, a₁⟩ = θ₀ ⟨x, cθ⟩ := by rw [← hθres]; rfl
    have r₂ : φ ⟨x, a₂⟩ = φ₀ ⟨x, cφ⟩ := by rw [← hφres]; rfl
    calc (θ' ⟨x, h₁⟩ : ℂ) * f₁ x = θ ⟨x, a₁⟩ := eθ.symm
      _ = θ₀ ⟨x, cθ⟩ := by rw [r₁]
      _ = φ₀ ⟨x, cφ⟩ := by rw [e₀, mul_one]
      _ = φ ⟨x, a₂⟩ := by rw [r₂]
      _ = (φ' ⟨x, h₂⟩ : ℂ) * f₂ x := eφ
  -- equal groups `J^{i+1}` for the two cores
  have hJ₁' : (simpleJGroup c₁.stratum.chain c₁.stratum.n c₁.stratum.b c₁.sequence.tail (i + 1) :
      Set G) = characterSelfIntertwining (θ'.comp ι₁) ∩ (S.chain.unitFiltration (i + 1) : Set G) := by
    rw [← hU₁]; exact hJ₁
  have hJ₂' : (simpleJGroup c₂.stratum.chain c₂.stratum.n c₂.stratum.b c₂.sequence.tail (i + 1) :
      Set G) = characterSelfIntertwining (φ'.comp ι₂) ∩ (S.chain.unitFiltration (i + 1) : Set G) := by
    rw [← hU₂]; exact hJ₂
  have hmemU₂ : ∀ h ∈ simpleHGroup c₂.stratum.chain c₂.stratum.n c₂.stratum.b c₂.sequence.tail
      (i + 1 + 1), (h : A) - 1 ∈ S.chain.endFiltration (((i + 1 + 1 : ℕ)) : ℤ) := by
    intro h hh
    have := (simpleHGroup_le_unitFiltration _ _ _ _ _ hh).2.2
    rwa [hU₂] at this
  have hmemU₁ : ∀ h ∈ simpleHGroup c₁.stratum.chain c₁.stratum.n c₁.stratum.b c₁.sequence.tail
      (i + 1 + 1), (h : A) - 1 ∈ S.chain.endFiltration (((i + 1 + 1 : ℕ)) : ℤ) := by
    intro h hh
    have := (simpleHGroup_le_unitFiltration _ _ _ _ _ hh).2.2
    rwa [hU₁] at this
  have hJ : simpleJGroup c₁.stratum.chain c₁.stratum.n c₁.stratum.b c₁.sequence.tail (i + 1) =
      simpleJGroup c₂.stratum.chain c₂.stratum.n c₂.stratum.b c₂.sequence.tail (i + 1) := by
    apply SetLike.coe_injective
    rw [hJ₁', hJ₂']
    ext g
    constructor
    · rintro ⟨hgI, hgU⟩
      refine ⟨mem_characterSelfIntertwining_of_relation hD (θ'.comp ι₁) (φ'.comp ι₂) f₁ f₂
        (fun x _ => elementCharacter_ne_zero ψF _ x)
        (fun x h₁ h₂ => key x _ _ (hD₁ ▸ h₁)) (fun h hh _ => ?_) hgI, hgU⟩
      exact ⟨elementCharacter_conj_eq_of_mem ψF hψ S.chain (by push_cast; omega) he₁ hgU
          (hmemU₂ h hh),
        elementCharacter_conj_eq_of_mem ψF hψ S.chain (by push_cast; omega) he₂ hgU
          (hmemU₂ h hh)⟩
    · rintro ⟨hgI, hgU⟩
      refine ⟨mem_characterSelfIntertwining_of_relation hD.symm (φ'.comp ι₂) (θ'.comp ι₁) f₂ f₁
        (fun x _ => elementCharacter_ne_zero ψF _ x)
        (fun x h₂ h₁ => (key x _ _ (hD₁ ▸ h₁)).symm) (fun h hh _ => ?_) hgI, hgU⟩
      exact ⟨elementCharacter_conj_eq_of_mem ψF hψ S.chain (by push_cast; omega) he₂ hgU
          (hmemU₁ h hh),
        elementCharacter_conj_eq_of_mem ψF hψ S.chain (by push_cast; omega) he₁ hgU
          (hmemU₁ h hh)⟩
  -- the commutator pairing identifies `H^{i+1}` inside the common `J^{i+1}`
  have hP₁ := mem_simpleHGroup_iff_commutator hpair ψF hψ
    (c₁.stratum.atDepthZero (hr₁0.trans_lt c₁.stratum.r_lt_n)) rfl hs₁
    (c₁.sequence.atDepthZero hr₁0) i hn₁.le hcrit₁ θ' hθ'
  have hP₂ := mem_simpleHGroup_iff_commutator hpair ψF hψ
    (c₂.stratum.atDepthZero (hr₂0.trans_lt c₂.stratum.r_lt_n)) rfl hs₂
    (c₂.sequence.atDepthZero hr₂0) i hn₂.le hcrit₂ φ' hφ'
  have hcomm₁ := (hgroups F V (c₁.stratum.atDepthZero (hr₁0.trans_lt c₁.stratum.r_lt_n)) rfl hs₁
    (c₁.sequence.atDepthZero hr₁0)).2.2.2.2 (i + 1) (i + 1) (by omega) (by omega)
  have hcomm₂ := (hgroups F V (c₂.stratum.atDepthZero (hr₂0.trans_lt c₂.stratum.r_lt_n)) rfl hs₂
    (c₂.sequence.atDepthZero hr₂0)).2.2.2.2 (i + 1) (i + 1) (by omega) (by omega)
  have hHδ : simpleHGroup c₁.stratum.chain c₁.stratum.n c₁.stratum.b c₁.sequence.tail (i + 1) =
      simpleHGroup c₂.stratum.chain c₂.stratum.n c₂.stratum.b c₂.sequence.tail (i + 1) := by
    ext x
    constructor
    · intro hx
      have hxJ₁ := hP₁.1 hx
      have hxJ₂ : x ∈ simpleJGroup c₂.stratum.chain c₂.stratum.n c₂.stratum.b
          c₂.sequence.tail (i + 1) := hJ ▸ hxJ₁
      refine (hP₂.2 x hxJ₂).2 fun y hy hc => ?_
      have hyJ₁ : y ∈ simpleJGroup c₁.stratum.chain c₁.stratum.n c₁.stratum.b
          c₁.sequence.tail (i + 1) := hJ.symm ▸ hy
      have hxy : ⁅x, y⁆ ∈ simpleHGroup c₁.stratum.chain c₁.stratum.n c₁.stratum.b
          c₁.sequence.tail (i + 1 + (i + 1)) :=
        hcomm₁ (Subgroup.commutator_mem_commutator hxJ₁ hyJ₁)
      have hc₁ : ⁅x, y⁆ ∈ simpleHGroup c₁.stratum.chain c₁.stratum.n c₁.stratum.b
          c₁.sequence.tail (i + 1) := simpleHGroup_antitone _ _ _ _ (by omega) hxy
      have hxy₂ : ⁅x, y⁆ ∈ simpleHGroup c₁.stratum.chain c₁.stratum.n c₁.stratum.b
          c₁.sequence.tail (i + 1 + 1) := simpleHGroup_antitone _ _ _ _ (by omega) hxy
      have h1 := (hP₁.2 x hxJ₁).1 hx y hyJ₁ hc₁
      have hk := key ⁅x, y⁆ hc₁ hc (hD₁ ▸ hxy₂)
      have hxy1 : ((⁅x, y⁆ : G) : A) - 1 ∈ S.chain.endFiltration ((i + 1 + (i + 1) : ℕ) : ℤ) := by
        have := (simpleHGroup_le_unitFiltration _ _ _ _ _ hxy).2.2
        rwa [hU₁] at this
      have hf₁ : f₁ ⁅x, y⁆ = 1 :=
        elementCharacter_eq_one_of_mem_endFiltration ψF hψ S.chain (by push_cast; omega) he₁ hxy1
      have hf₂ : f₂ ⁅x, y⁆ = 1 :=
        elementCharacter_eq_one_of_mem_endFiltration ψF hψ S.chain (by push_cast; omega) he₂ hxy1
      rw [hf₁, hf₂, mul_one, mul_one] at hk
      exact (Units.ext hk.symm).trans h1
    · intro hx
      have hxJ₂ := hP₂.1 hx
      have hxJ₁ : x ∈ simpleJGroup c₁.stratum.chain c₁.stratum.n c₁.stratum.b
          c₁.sequence.tail (i + 1) := hJ.symm ▸ hxJ₂
      refine (hP₁.2 x hxJ₁).2 fun y hy hc => ?_
      have hyJ₂ : y ∈ simpleJGroup c₂.stratum.chain c₂.stratum.n c₂.stratum.b
          c₂.sequence.tail (i + 1) := hJ ▸ hy
      have hxy : ⁅x, y⁆ ∈ simpleHGroup c₂.stratum.chain c₂.stratum.n c₂.stratum.b
          c₂.sequence.tail (i + 1 + (i + 1)) :=
        hcomm₂ (Subgroup.commutator_mem_commutator hxJ₂ hyJ₂)
      have hc₂ : ⁅x, y⁆ ∈ simpleHGroup c₂.stratum.chain c₂.stratum.n c₂.stratum.b
          c₂.sequence.tail (i + 1) := simpleHGroup_antitone _ _ _ _ (by omega) hxy
      have hxy₂ : ⁅x, y⁆ ∈ simpleHGroup c₂.stratum.chain c₂.stratum.n c₂.stratum.b
          c₂.sequence.tail (i + 1 + 1) := simpleHGroup_antitone _ _ _ _ (by omega) hxy
      have h1 := (hP₂.2 x hxJ₂).1 hx y hyJ₂ hc₂
      have hk := key ⁅x, y⁆ hc hc₂ (hD₁ ▸ hD.symm ▸ hxy₂)
      have hxy1 : ((⁅x, y⁆ : G) : A) - 1 ∈ S.chain.endFiltration ((i + 1 + (i + 1) : ℕ) : ℤ) := by
        have := (simpleHGroup_le_unitFiltration _ _ _ _ _ hxy).2.2
        rwa [hU₂] at this
      have hf₁ : f₁ ⁅x, y⁆ = 1 :=
        elementCharacter_eq_one_of_mem_endFiltration ψF hψ S.chain (by push_cast; omega) he₁ hxy1
      have hf₂ : f₂ ⁅x, y⁆ = 1 :=
        elementCharacter_eq_one_of_mem_endFiltration ψF hψ S.chain (by push_cast; omega) he₂ hxy1
      rw [hf₁, hf₂, mul_one, mul_one] at hk
      exact (Units.ext hk).trans h1
  exact c₁.domain_eq.trans (hHδ.trans c₂.domain_eq.symm)

section Pairs

variable {K : Type*} [Group K]

/-- Two subgroup–character pairs coincide exactly when the subgroups coincide and the
characters agree pointwise. -/
theorem characterPair_mk_eq_iff {H₁ H₂ : Subgroup K} (θ : H₁ →* ℂˣ) (φ : H₂ →* ℂˣ) :
    (⟨H₁, θ⟩ : CharacterPair K) = ⟨H₂, φ⟩ ↔
      H₁ = H₂ ∧ characterAgreesOn H₁ θ φ (fun _ => 1) := by
  constructor
  · intro h
    obtain ⟨rfl, hh⟩ := Sigma.mk.inj_iff.mp h
    obtain rfl := eq_of_heq hh
    exact ⟨rfl, fun g => ⟨g.2, g.2, (mul_one _).symm⟩⟩
  · rintro ⟨rfl, hag⟩
    congr
    ext g
    obtain ⟨h₁, h₂, he⟩ := hag g
    rw [mul_one] at he
    exact he

/-- Images of two character sets in the pairs coincide, for a nonempty first set, exactly when
the domains coincide and the sets correspond under pointwise agreement. -/
theorem characterPair_image_eq_iff {H₁ H₂ : Subgroup K} (C₁ : Set (H₁ →* ℂˣ))
    (C₂ : Set (H₂ →* ℂˣ)) (hC : C₁.Nonempty) :
    (fun θ => (⟨H₁, θ⟩ : CharacterPair K)) '' C₁ = (fun φ => (⟨H₂, φ⟩ : CharacterPair K)) '' C₂ ↔
      H₁ = H₂ ∧ CharacterSetTwistCorrespondence C₁ C₂ (fun _ => 1) := by
  constructor
  · intro h
    obtain ⟨θ, hθ⟩ := hC
    obtain ⟨φ, hφ, hφθ⟩ := h ▸ (Set.mem_image_of_mem _ hθ : _ ∈ (fun θ => (⟨H₁, θ⟩ :
      CharacterPair K)) '' C₁)
    have hH : H₁ = H₂ := ((characterPair_mk_eq_iff φ θ).mp hφθ).1.symm
    subst hH
    refine ⟨rfl, fun θ hθ => ?_, fun φ hφ => ?_⟩
    · obtain ⟨φ, hφ, he⟩ := h ▸ (Set.mem_image_of_mem _ hθ : _ ∈ (fun θ => (⟨H₁, θ⟩ :
        CharacterPair K)) '' C₁)
      exact ⟨φ, hφ, ((characterPair_mk_eq_iff θ φ).mp he.symm).2⟩
    · obtain ⟨θ, hθ, he⟩ := h.symm ▸ (Set.mem_image_of_mem _ hφ : _ ∈ (fun φ => (⟨H₁, φ⟩ :
        CharacterPair K)) '' C₂)
      exact ⟨θ, hθ, ((characterPair_mk_eq_iff θ φ).mp he).2⟩
  · rintro ⟨rfl, h₁, h₂⟩
    ext P
    constructor
    · rintro ⟨θ, hθ, rfl⟩
      obtain ⟨φ, hφ, he⟩ := h₁ θ hθ
      exact ⟨φ, hφ, ((characterPair_mk_eq_iff θ φ).mpr ⟨rfl, he⟩).symm⟩
    · rintro ⟨φ, hφ, rfl⟩
      obtain ⟨θ, hθ, he⟩ := h₂ φ hφ
      exact ⟨θ, hθ, (characterPair_mk_eq_iff θ φ).mpr ⟨rfl, he⟩⟩

end Pairs

/-- **Choice independence of the pairs.** For a simple stratum at a nonnegative index and a depth
below the level, the image of the simple characters of any defining sequence is the set
`simpleCharacterPairs`. This uses the first clause of `SimpleCharacterChoiceStatement`. -/
theorem simpleCharacterPairs_eq_image (hchoice : SimpleCharacterChoiceStatement.{u, v})
    (ψF : AddChar F ℂ) (hψ : IsBKAdditiveCharacter ψF) {S : Stratum 𝒪[F] F V}
    (hs : S.IsSimple) (hr : 0 ≤ S.r) (q : S.DefiningSequenceChoice) (k : ℕ)
    (hk : (k : ℤ) < S.n) :
    simpleCharacterPairs ψF S k =
      (fun θ => (⟨simpleHGroup S.chain S.n S.b q.tail (k + 1), θ⟩ : CharacterPair G)) ''
        simpleCharacters ψF S.chain S.n S.b q.tail k := by
  have himage (q' : S.DefiningSequenceChoice) :
      (fun θ => (⟨simpleHGroup S.chain S.n S.b q'.tail (k + 1), θ⟩ : CharacterPair G)) ''
        simpleCharacters ψF S.chain S.n S.b q'.tail k =
      (fun θ => (⟨simpleHGroup S.chain S.n S.b q.tail (k + 1), θ⟩ : CharacterPair G)) ''
        simpleCharacters ψF S.chain S.n S.b q.tail k := by
    obtain ⟨hH, hC⟩ := (hchoice F V ψF hψ (S.atDepthZero (hr.trans_lt S.r_lt_n)) rfl
      (Stratum.isSimple_atDepthZero hs hr) (q.atDepthZero hr)).1 (q'.atDepthZero hr) k hk
    change simpleHGroup S.chain S.n S.b q.tail (k + 1) =
      simpleHGroup S.chain S.n S.b q'.tail (k + 1) at hH
    change simpleCharacters ψF S.chain S.n S.b q'.tail k = characterSetTwist _
      (simpleCharacters ψF S.chain S.n S.b q.tail k) (fun _ => 1) at hC
    ext P
    constructor
    · rintro ⟨φ, hφ, rfl⟩
      rw [hC] at hφ
      obtain ⟨θ, hθ, he⟩ := hφ
      exact ⟨θ, hθ, ((characterPair_mk_eq_iff φ θ).mpr ⟨hH.symm, he⟩).symm⟩
    · rintro ⟨θ, hθ, rfl⟩
      let φ : simpleHGroup S.chain S.n S.b q'.tail (k + 1) →* ℂˣ :=
        θ.comp (Subgroup.inclusion hH.symm.le)
      have he : characterAgreesOn (simpleHGroup S.chain S.n S.b q'.tail (k + 1)) φ θ (fun _ => 1) :=
        fun g => ⟨g.2, hH.symm ▸ g.2, (mul_one _).symm⟩
      refine ⟨φ, ?_, (characterPair_mk_eq_iff φ θ).mpr ⟨hH.symm, he⟩⟩
      rw [hC]
      exact ⟨θ, hθ, he⟩
  ext P
  simp only [simpleCharacterPairs, Set.mem_iUnion]
  constructor
  · rintro ⟨q', hP⟩
    rwa [himage q'] at hP
  · intro hP
    exact ⟨q, hP⟩

/-- Equal sets of pairs at a depth below the level give equal domains and corresponding
character sets for every choice of defining sequences, and these sets are nonempty. -/
theorem simpleCharacters_correspond_of_pairs_eq
    (hrestriction : SimpleCharacterRestrictionStatement.{u, v})
    (hchoice : SimpleCharacterChoiceStatement.{u, v})
    (ψF : AddChar F ℂ) (hψ : IsBKAdditiveCharacter ψF) {S T : Stratum 𝒪[F] F V}
    (hsS : S.IsSimple) (hsT : T.IsSimple) (hrS : 0 ≤ S.r) (hrT : 0 ≤ T.r)
    (q : S.DefiningSequenceChoice) (q' : T.DefiningSequenceChoice) (k : ℕ)
    (hkS : (k : ℤ) < S.n) (hkT : (k : ℤ) < T.n)
    (h : simpleCharacterPairs ψF S k = simpleCharacterPairs ψF T k) :
    simpleHGroup S.chain S.n S.b q.tail (k + 1) = simpleHGroup T.chain T.n T.b q'.tail (k + 1) ∧
      CharacterSetTwistCorrespondence (simpleCharacters ψF S.chain S.n S.b q.tail k)
        (simpleCharacters ψF T.chain T.n T.b q'.tail k) (fun _ => 1) ∧
      (simpleCharacters ψF S.chain S.n S.b q.tail k).Nonempty := by
  have hne : (simpleCharacters ψF S.chain S.n S.b q.tail k).Nonempty :=
    (hrestriction F V ψF hψ (S.atDepthZero (hrS.trans_lt S.r_lt_n)) rfl
      (Stratum.isSimple_atDepthZero hsS hrS) (q.atDepthZero hrS)).2.2.2.2 k hkS
  rw [simpleCharacterPairs_eq_image hchoice ψF hψ hsS hrS q k hkS,
    simpleCharacterPairs_eq_image hchoice ψF hψ hsT hrT q' k hkT] at h
  obtain ⟨hH, hC⟩ := (characterPair_image_eq_iff _ _ hne).mp h
  exact ⟨hH, hC, hne⟩

/-- **The first assertion of BK93 (3.5.9).** Let `[𝔄,n,i+1,β₁]` and `[𝔄,n,i+1,β₂]` be simple
strata on the same lattice chain with the same sets of simple character pairs at depth `i+1`.
Then `H^{i+1}(β₁,𝔄) = H^{i+1}(β₂,𝔄)` for every choice of defining sequences. -/
theorem simpleHGroup_eq_of_simpleCharacterPairs_eq
    (hgroups : SimpleStratumGroupPropertiesStatement.{u, v})
    (hrestriction : SimpleCharacterRestrictionStatement.{u, v})
    (hchoice : SimpleCharacterChoiceStatement.{u, v})
    (hint : SimpleCharacterIntertwiningStatement.{u, v})
    (hpair : SimpleCharacterPairingStatement.{u, v})
    (ψF : AddChar F ℂ) (hψ : IsBKAdditiveCharacter ψF) (L : LatticeChain 𝒪[F] F V) (n : ℤ)
    (i : ℕ) (S T : SimpleStratumAt L n ((i + 1 : ℕ) : ℤ))
    (h : simpleCharacterPairs ψF S.1 (i + 1) = simpleCharacterPairs ψF T.1 (i + 1))
    (q : S.1.DefiningSequenceChoice) (q' : T.1.DefiningSequenceChoice) :
    simpleHGroup L n S.1.b q.tail (i + 1) = simpleHGroup L n T.1.b q'.tail (i + 1) := by
  obtain ⟨hLS, hnS, hrS, hsS⟩ := S.2
  obtain ⟨hLT, hnT, hrT, hsT⟩ := T.2
  have e₁ : simpleHGroup L n S.1.b q.tail (i + 1) =
      simpleHGroup S.1.chain S.1.n S.1.b q.tail (i + 1) := by rw [hLS, hnS]
  have e₂ : simpleHGroup L n T.1.b q'.tail (i + 1) =
      simpleHGroup T.1.chain T.1.n T.1.b q'.tail (i + 1) := by rw [hLT, hnT]
  rw [e₁, e₂]
  have hr0S : 0 ≤ S.1.r := by rw [hrS]; positivity
  have hr0T : 0 ≤ T.1.r := by rw [hrT]; positivity
  have hkS : ((i + 1 : ℕ) : ℤ) < S.1.n := by have := S.1.r_lt_n; omega
  have hkT : ((i + 1 : ℕ) : ℤ) < T.1.n := by have := T.1.r_lt_n; omega
  have hL : T.1.chain = S.1.chain := hLT.trans hLS.symm
  have hn : T.1.n = S.1.n := hnT.trans hnS.symm
  by_cases hi : (i : ℤ) < S.1.n / 2
  · obtain ⟨hH, hC, θ₀, hθ₀⟩ := simpleCharacters_correspond_of_pairs_eq hrestriction hchoice ψF hψ
      hsS hsT hr0S hr0T q q' (i + 1) hkS hkT h
    obtain ⟨φ₀, hφ₀, hag⟩ := hC.1 θ₀ hθ₀
    exact simpleHGroup_eq_of_common_character_of_lt_half hgroups hrestriction hint hpair ψF hψ
      S.1 T.1 hL hn hsS hsT i hr0S (by rw [hrS]; push_cast; omega) hr0T
      (by rw [hrT]; push_cast; omega) hi q q' hH θ₀ hθ₀ φ₀ hφ₀ hag
  · have hS' := (simpleCharacterHighIndex.{u, v} F V ψF hψ S.1 q i (by omega)).1
    have hT' := (simpleCharacterHighIndex.{u, v} F V ψF hψ T.1 q' i (by rw [hn]; omega)).1
    rw [hS', hT', hL]

/-- **The first assertion of BK93 (3.5.9) from published simple-character statements.**
The subgroup properties, restriction, choice independence, intertwining and commutator pairing
statements imply: if two simple strata `[𝔄,n,m,β₁]`, `[𝔄,n,m,β₂]` on the same lattice chain,
with `m ≥ 1`, have equal sets of simple character pairs at depth `m`, then
`H^m(β₁,𝔄) = H^m(β₂,𝔄)` for all defining sequences. -/
def SimpleCharacterLoweringGroupsReductionStatement : Prop :=
  SimpleStratumGroupPropertiesStatement.{uF, uV} → SimpleCharacterRestrictionStatement.{uF, uV} →
    SimpleCharacterChoiceStatement.{uF, uV} → SimpleCharacterIntertwiningStatement.{uF, uV} →
    SimpleCharacterPairingStatement.{uF, uV} →
    ∀ (F : Type uF) [Field F] [ValuativeRel F] [TopologicalSpace F]
      [IsNonarchimedeanLocalField F] (V : Type uV) [AddCommGroup V] [Module F V]
      (ψF : AddChar F ℂ), IsBKAdditiveCharacter ψF →
      ∀ (L : LatticeChain 𝒪[F] F V) (n : ℤ) (m : ℕ), 1 ≤ m →
      ∀ (S T : SimpleStratumAt L n m),
        simpleCharacterPairs ψF S.1 m = simpleCharacterPairs ψF T.1 m →
        ∀ (q : S.1.DefiningSequenceChoice) (q' : T.1.DefiningSequenceChoice),
          simpleHGroup L n S.1.b q.tail m = simpleHGroup L n T.1.b q'.tail m

theorem simpleCharacterLoweringGroupsReduction :
    SimpleCharacterLoweringGroupsReductionStatement.{uF, uV} := by
  intro hgroups hrestriction hchoice hint hpair F _ _ _ _ V _ _ ψF hψ L n m hm S T h q q'
  obtain ⟨i, rfl⟩ : ∃ i, m = i + 1 := ⟨m - 1, by omega⟩
  exact simpleHGroup_eq_of_simpleCharacterPairs_eq hgroups hrestriction hchoice hint hpair ψF hψ
    L n i S T h q q'

end Langlands.BushnellKutzko
