import Langlands.BushnellKutzko.SimpleCharacterLoweringSets
import Langlands.BushnellKutzko.UnitFiltrationCharacterExtension
import Langlands.BushnellKutzko.PureStratumSimpleApproximationStatement
import Langlands.BushnellKutzko.SimpleCharacterLoweringStatement
import Langlands.BushnellKutzko.SimpleCharacterTransferIntersection
import Langlands.BushnellKutzko.SimpleCharacterNormalizerRestriction
import Langlands.BushnellKutzko.SimpleStratumIntertwinedRefinement

/-! # Lowering the simple-character level (BK93 (3.5.9)): the refinement argument -/

noncomputable section

open ValuativeRel
open scoped Pointwise

namespace Langlands.BushnellKutzko

universe u v uF uV

section Characters

variable {K : Type*} [Group K]

/-- Equal subgroups carrying pointwise agreeing characters give the same normalizer. -/
theorem characterNormalizer_eq_of_agree {H₁ H₂ : Subgroup K} (h : H₁ = H₂)
    (χ₁ : H₁ →* ℂˣ) (χ₂ : H₂ →* ℂˣ) (hag : characterAgreesOn H₁ χ₁ χ₂ (fun _ => 1)) :
    characterNormalizer χ₁ = characterNormalizer χ₂ := by
  subst h
  have : χ₁ = χ₂ := by
    ext g
    obtain ⟨h₁, h₂, e⟩ := hag g
    rw [mul_one] at e
    exact e
  rw [this]

/-- The normalizer of a character is closed under inversion. -/
theorem inv_mem_characterNormalizer {H : Subgroup K} {χ : H →* ℂˣ} {x : K}
    (hx : x ∈ characterNormalizer χ) : x⁻¹ ∈ characterNormalizer χ := by
  refine ⟨Subgroup.inv_mem _ hx.1, fun h hh => ?_⟩
  have hh' : (h : K) ∈ H := h.2
  have h₁ : x * (x⁻¹ * (h : K) * x⁻¹⁻¹) * x⁻¹ ∈ H := by
    simp [mul_assoc]
  have e := hx.2 ⟨_, hh⟩ h₁
  have e₁ : (⟨x * (x⁻¹ * (h : K) * x⁻¹⁻¹) * x⁻¹, h₁⟩ : H) = h := Subtype.ext (by group)
  rw [e₁] at e
  exact e.symm

end Characters

variable {F : Type u} [Field F] [ValuativeRel F] [TopologicalSpace F]
  [IsNonarchimedeanLocalField F] {V : Type v} [AddCommGroup V] [Module F V]

local notation "A" => Module.End F V
local notation "G" => (Module.End F V)ˣ

omit [TopologicalSpace F] [IsNonarchimedeanLocalField F] in
/-- The index of a simple stratum lies below its critical depth. -/
theorem Stratum.IsSimple.lt_simpleCriticalDepth {S : Stratum 𝒪[F] F V} (hS : S.IsSimple) :
    (S.r : WithTop ℤ) < simpleCriticalDepth S.chain S.b := by
  have h := hS.2
  unfold simpleCriticalDepth
  cases hc : criticalExponent S.chain S.b with
  | bot => exact WithTop.coe_lt_top _
  | coe c =>
    rw [hc] at h
    have h' : c < -S.r := WithBot.coe_lt_coe.mp h
    exact WithTop.coe_lt_coe.mpr (by omega)

omit [TopologicalSpace F] [IsNonarchimedeanLocalField F] in
/-- The commutator of `x ∈ U^1(𝔄)` with `y ∈ U^k(𝔄)` lies in `U^{k+1}(𝔄)`. -/
theorem LatticeChain.commutator_mem_unitFiltration_succ (L : LatticeChain 𝒪[F] F V) {k : ℕ}
    {x y : G} (hx : x ∈ L.unitFiltration 1) (hy : y ∈ L.unitFiltration k) :
    x * y * x⁻¹ * y⁻¹ ∈ L.unitFiltration (k + 1) := by
  have hx0 : x ∈ L.unitFiltration 0 := L.unitFiltration_antitone (Nat.zero_le 1) hx
  have hy0 : y ∈ L.unitFiltration 0 := L.unitFiltration_antitone (Nat.zero_le k) hy
  have h0 : x * y * x⁻¹ * y⁻¹ ∈ L.unitFiltration 0 :=
    (L.unitFiltration 0).mul_mem ((L.unitFiltration 0).mul_mem
      ((L.unitFiltration 0).mul_mem hx0 hy0) ((L.unitFiltration 0).inv_mem hx0))
      ((L.unitFiltration 0).inv_mem hy0)
  refine ⟨h0.1, h0.2.1, ?_⟩
  have he : ((x * y * x⁻¹ * y⁻¹ : G) : A) - 1 =
      (((x : A) - 1) * ((y : A) - 1) - ((y : A) - 1) * ((x : A) - 1)) *
        ((x⁻¹ : G) : A) * ((y⁻¹ : G) : A) := by
    have hx' : (x : A) * ((x⁻¹ : G) : A) = 1 := Units.mul_inv x
    have hy' : (y : A) * ((y⁻¹ : G) : A) = 1 := Units.mul_inv y
    simp only [Units.val_mul]
    calc (x : A) * y * ((x⁻¹ : G) : A) * ((y⁻¹ : G) : A) - 1
        = (x : A) * y * ((x⁻¹ : G) : A) * ((y⁻¹ : G) : A) -
            (y : A) * x * ((x⁻¹ : G) : A) * ((y⁻¹ : G) : A) := by
          rw [mul_assoc (y : A) (x : A), hx', mul_one, hy']
      _ = _ := by noncomm_ring
  rw [he]
  have hxk : (x : A) - 1 ∈ L.endFiltration 1 := hx.2.2
  have hyk : (y : A) - 1 ∈ L.endFiltration k := hy.2.2
  have hxi : ((x⁻¹ : G) : A) ∈ L.endFiltration 0 := (L.mem_order_iff_mem_endFiltration).1 hx.2.1
  have hyi : ((y⁻¹ : G) : A) ∈ L.endFiltration 0 := (L.mem_order_iff_mem_endFiltration).1 hy.2.1
  have h1 : ((x : A) - 1) * ((y : A) - 1) ∈ L.endFiltration ((k + 1 : ℕ) : ℤ) := by
    have := L.mul_mem_endFiltration hxk hyk
    rwa [show (1 : ℤ) + k = ((k + 1 : ℕ) : ℤ) by push_cast; ring] at this
  have h2 : ((y : A) - 1) * ((x : A) - 1) ∈ L.endFiltration ((k + 1 : ℕ) : ℤ) := by
    have := L.mul_mem_endFiltration hyk hxk
    rwa [show (k : ℤ) + 1 = ((k + 1 : ℕ) : ℤ) by push_cast; ring] at this
  have h3 := L.mul_mem_endFiltration (L.mul_mem_endFiltration (sub_mem h1 h2) hxi) hyi
  simpa using h3

omit [TopologicalSpace F] [IsNonarchimedeanLocalField F] in
/-- At a depth `m` with `1 ≤ m < r`, where `r = finiteCriticalDepth` is `−k₀(β,𝔄)` for
nonscalar `β` and the level `n` for scalar `β`, the outer factor of the intertwining formula
lies in `U^1(𝔄)`. -/
theorem simpleCharacterIntertwiningFactor_subset_unitFiltration_one (S : Stratum 𝒪[F] F V)
    (q : S.DefiningSequenceChoice) (m : ℕ) (hm : 1 ≤ m)
    (hmr : (m : ℤ) < finiteCriticalDepth S.chain S.n S.b) :
    simpleCharacterIntertwiningFactor S q m ⊆ (S.chain.unitFiltration 1 : Set G) := by
  intro g hg
  unfold simpleCharacterIntertwiningFactor at hg
  split_ifs at hg with hb
  · rw [Set.mem_singleton_iff.mp hg]
    exact (S.chain.unitFiltration 1).one_mem
  · set r := finiteCriticalDepth S.chain S.n S.b with hr
    have hQN : centralizerLattice S.chain S.b (r - m) * adjointLattice S.chain S.b (-r) ≤
        S.chain.endFiltration 1 := by
      apply Submodule.mul_le.mpr
      intro a ha z hz
      have h := S.chain.mul_mem_endFiltration ha.1 hz.1
      have h' : a * z ∈ S.chain.endFiltration (r - m) := by simpa using h
      exact S.chain.endFiltration_antitone (show (1 : ℤ) ≤ r - m by omega) h'
    have hJ : simpleJLayer S.chain S.n S.b q.tail (simpleJCutoff r).toNat ≤
        S.chain.endFiltration 1 := by
      intro x hx
      exact S.chain.endFiltration_antitone (by unfold simpleJCutoff; omega) hx.2
    have hg1 : (g : A) - 1 ∈ S.chain.endFiltration ((1 : ℕ) : ℤ) := by
      have := sup_le hQN hJ hg
      simpa using this
    obtain ⟨g', hg', hval⟩ := S.chain.exists_mem_unitFiltration le_rfl hg1
    have heq : g' = g := Units.ext (by rw [hval]; abel)
    exact heq ▸ hg'

/-- **The second assertion of BK93 (3.5.9) by the refinement argument.** -/
theorem exists_equivalent_simpleCharacterPairs_pred_eq
    (hgroups : SimpleStratumGroupPropertiesStatement.{u, v})
    (hrestriction : SimpleCharacterRestrictionStatement.{u, v})
    (hchoice : SimpleCharacterChoiceStatement.{u, v})
    (hint : SimpleCharacterIntertwiningStatement.{u, v})
    (hpair : SimpleCharacterPairingStatement.{u, v})
    (hcoh : SimpleCharacterCoherenceStatement.{u, v})
    (hnorm : SimpleCharacterNormalizerRestrictionStatement.{u, v})
    (happrox : PureStratumSimpleApproximationStatement.{u, v})
    (ψF : AddChar F ℂ) (hψ : IsBKAdditiveCharacter ψF) (L : LatticeChain 𝒪[F] F V) (n : ℤ)
    (i : ℕ) (S T : SimpleStratumAt L n ((i + 1 : ℕ) : ℤ))
    (h : simpleCharacterPairs ψF S.1 (i + 1) = simpleCharacterPairs ψF T.1 (i + 1))
    (q : S.1.DefiningSequenceChoice) (q' : T.1.DefiningSequenceChoice) :
    ∃ S' : SimpleStratumAt L n ((i + 1 : ℕ) : ℤ), S'.1.Equivalent S.1 ∧
      simpleCharacterPairs ψF S'.1 i = simpleCharacterPairs ψF T.1 i := by
  have := L.finiteDimensional
  obtain ⟨hLS, hnS, hrS, hsS⟩ := S.2
  obtain ⟨hLT, hnT, hrT, hsT⟩ := T.2
  have hr0S : 0 ≤ S.1.r := by rw [hrS]; positivity
  have hr0T : 0 ≤ T.1.r := by rw [hrT]; positivity
  have hkS : ((i + 1 : ℕ) : ℤ) < S.1.n := by have := S.1.r_lt_n; omega
  have hkT : ((i + 1 : ℕ) : ℤ) < T.1.n := by have := T.1.r_lt_n; omega
  have hiS : (i : ℤ) < S.1.n := by push_cast at hkS; omega
  have hiT : (i : ℤ) < T.1.n := by push_cast at hkT; omega
  have hcS : (((i + 1 : ℕ) : ℤ) : WithTop ℤ) < simpleCriticalDepth S.1.chain S.1.b := by
    have h₁ := hsS.lt_simpleCriticalDepth; rwa [hrS] at h₁
  have hcT : (((i + 1 : ℕ) : ℤ) : WithTop ℤ) < simpleCriticalDepth T.1.chain T.1.b := by
    have h₁ := hsT.lt_simpleCriticalDepth; rwa [hrT] at h₁
  have hcS' : ((i : ℤ) : WithTop ℤ) < simpleCriticalDepth S.1.chain S.1.b :=
    lt_of_le_of_lt (WithTop.coe_le_coe.mpr (by push_cast; omega)) hcS
  have hcT' : ((i : ℤ) : WithTop ℤ) < simpleCriticalDepth T.1.chain T.1.b :=
    lt_of_le_of_lt (WithTop.coe_le_coe.mpr (by push_cast; omega)) hcT
  have hfT : ((i + 1 : ℕ) : ℤ) < finiteCriticalDepth T.1.chain T.1.n T.1.b := by
    unfold finiteCriticalDepth
    cases hd : simpleCriticalDepth T.1.chain T.1.b with
    | top => simpa using hkT
    | coe d => rw [hd] at hcT; simpa using WithTop.coe_lt_coe.mp hcT
  -- a common character at depth `i + 1` and its lifts
  obtain ⟨hH, hC, θ₀, hθ₀⟩ := simpleCharacters_correspond_of_pairs_eq hrestriction hchoice ψF hψ
    hsS hsT hr0S hr0T q q' (i + 1) hkS hkT h
  obtain ⟨φ₀, hφ₀, hag⟩ := hC.1 θ₀ hθ₀
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
  have hHm : simpleHGroup S.1.chain S.1.n S.1.b q.tail (i + 1) =
      simpleHGroup T.1.chain T.1.n T.1.b q'.tail (i + 1) := by
    have h₁ := simpleHGroup_eq_of_simpleCharacterPairs_eq hgroups hrestriction hchoice hint hpair
      ψF hψ L n i S T h q q'
    rw [hLS, hnS, hLT, hnT]
    exact h₁
  have hs₀ := Stratum.isSimple_atDepthZero hsS hr0S
  have ht₀ := Stratum.isSimple_atDepthZero hsT hr0T
  have hLTS : T.1.chain = S.1.chain := hLT.trans hLS.symm
  -- the exact carrier of `H^{i+1}` for the first stratum
  have hcarS := (hgroups F V (S.1.atDepthZero (hr0S.trans_lt S.1.r_lt_n)) rfl hs₀
    (q.atDepthZero hr0S)).1
  have hsuccS : ∀ g : G, g ∈ simpleHGroup S.1.chain S.1.n S.1.b q.tail (i + 1) →
      g ∈ S.1.chain.unitFiltration (i + 1 + 1) →
      g ∈ simpleHGroup S.1.chain S.1.n S.1.b q.tail (i + 1 + 1) := by
    intro g hg hgU
    have hc₁ : (simpleHGroup S.1.chain S.1.n S.1.b q.tail (i + 1) : Set G) =
        simpleHCarrier S.1.chain S.1.n S.1.b q.tail (i + 1) := (hcarS (i + 1)).1
    have hc₂ : (simpleHGroup S.1.chain S.1.n S.1.b q.tail (i + 1 + 1) : Set G) =
        simpleHCarrier S.1.chain S.1.n S.1.b q.tail (i + 1 + 1) := (hcarS (i + 1 + 1)).1
    have hg' : g ∈ (simpleHGroup S.1.chain S.1.n S.1.b q.tail (i + 1) : Set G) := hg
    rw [hc₁] at hg'
    change g ∈ (simpleHGroup S.1.chain S.1.n S.1.b q.tail (i + 1 + 1) : Set G)
    rw [hc₂]
    exact ⟨hgU, hg'.2⟩
  -- the quotient of the lifts and its additive description
  let φS := φ.comp (Subgroup.inclusion hHm.le)
  let χ := φS / θ
  have hval : ∀ g : simpleHGroup S.1.chain S.1.n S.1.b q.tail (i + 1),
      (g : G) ∈ simpleHGroup S.1.chain S.1.n S.1.b q.tail (i + 1 + 1) → θ g = φS g := by
    intro g hg
    obtain ⟨h₁, h₂, e⟩ := hag ⟨g, hg⟩
    have eθ : θ g = θ₀ ⟨g, h₁⟩ := by rw [← hθres]; rfl
    have eφ : φS g = φ₀ ⟨g, h₂⟩ := by rw [← hφres]; rfl
    rw [eθ, eφ]
    exact Units.ext (by rw [e, mul_one])
  have hχtriv : ∀ g : simpleHGroup S.1.chain S.1.n S.1.b q.tail (i + 1),
      (g : G) ∈ S.1.chain.unitFiltration (i + 1 + 1) → χ g = 1 := by
    intro g hg
    change φS g / θ g = 1
    rw [hval g (hsuccS g g.2 hg), div_self']
  obtain ⟨b, hb, hbχ⟩ := exists_elementCharacter_eq_of_trivial_on_succ ψF hψ.1 hψ.2 S.1.chain i
    (simpleHGroup S.1.chain S.1.n S.1.b q.tail (i + 1))
    (simpleHGroup_le_unitFiltration _ _ _ _ _) χ hχtriv
  -- intertwining and normalizers from (3.3.2), (3.3.17) and (3.5.10)
  have hBθ := centralizerUnitGroup_subset_selfIntertwining hint ψF hψ
    (S.1.atDepthZero (hr0S.trans_lt S.1.r_lt_n)) rfl hs₀ (q.atDepthZero hr0S) i hiS hcS' hθ
  have hBθ₀ := centralizerUnitGroup_subset_selfIntertwining hint ψF hψ
    (S.1.atDepthZero (hr0S.trans_lt S.1.r_lt_n)) rfl hs₀ (q.atDepthZero hr0S) (i + 1) hkS hcS hθ₀
  have hBφ := centralizerUnitGroup_subset_selfIntertwining hint ψF hψ
    (T.1.atDepthZero (hr0T.trans_lt T.1.r_lt_n)) rfl ht₀ (q'.atDepthZero hr0T) i hiT hcT' hφ
  have hI₀ := characterSelfIntertwining_eq_of_agree hH θ₀ φ₀ hag
  have hN₀ := characterNormalizer_eq_of_agree hH θ₀ φ₀ hag
  have hIφ₀ := (hint F V ψF hψ (T.1.atDepthZero (hr0T.trans_lt T.1.r_lt_n)) rfl ht₀
    (q'.atDepthZero hr0T) (i + 1) hkT hcT φ₀ hφ₀).1
  have hYN := simpleCharacterIntertwiningFactor_subset_normalizer hint ψF hψ
    (T.1.atDepthZero (hr0T.trans_lt T.1.r_lt_n)) rfl ht₀ (q'.atDepthZero hr0T) (i + 1) hkT hcT hφ₀
  have hYU := simpleCharacterIntertwiningFactor_subset_unitFiltration_one
    (T.1.atDepthZero (hr0T.trans_lt T.1.r_lt_n)) (q'.atDepthZero hr0T) (i + 1) (by omega) hfT
  have hnormS := hnorm F V ψF hψ (S.1.atDepthZero (hr0S.trans_lt S.1.r_lt_n)) rfl hs₀
    (q.atDepthZero hr0S) i (by change (i : ℤ) + 1 < S.1.n; push_cast at hkS; omega) hcS θ hθ
  -- `χ` is invariant under conjugation by normalizing elements of `U^1`
  have hχconj : ∀ x : G, x ∈ S.1.chain.unitFiltration 1 →
      x ∈ Subgroup.normalizer (simpleHGroup S.1.chain S.1.n S.1.b q.tail (i + 1) : Set G) →
      ∀ (y : G) (hy : y ∈ simpleHGroup S.1.chain S.1.n S.1.b q.tail (i + 1))
        (hxy : x * y * x⁻¹ ∈ simpleHGroup S.1.chain S.1.n S.1.b q.tail (i + 1)),
        χ ⟨_, hxy⟩ = χ ⟨y, hy⟩ := by
    intro x hxU _ y hy hxy
    have hc : x * y * x⁻¹ * y⁻¹ ∈ simpleHGroup S.1.chain S.1.n S.1.b q.tail (i + 1) :=
      Subgroup.mul_mem _ hxy (Subgroup.inv_mem _ hy)
    have hcU := S.1.chain.commutator_mem_unitFiltration_succ hxU
      (simpleHGroup_le_unitFiltration _ _ _ _ _ hy)
    have e : (⟨x * y * x⁻¹, hxy⟩ : simpleHGroup S.1.chain S.1.n S.1.b q.tail (i + 1)) =
        ⟨_, hc⟩ * ⟨y, hy⟩ := Subtype.ext (by simp)
    rw [e, map_mul, hχtriv ⟨_, hc⟩ hcU, one_mul]
  have hsplit : ∀ g : simpleHGroup S.1.chain S.1.n S.1.b q.tail (i + 1), φS g = θ g * χ g := by
    intro g
    simp only [χ, MonoidHom.div_apply, mul_div_cancel]
  -- the intertwining of `ψ_b` on `U^{i+1}(𝔅_{β₁})`
  have hE2 : ∀ t ∈ centralizerUnitGroup S.1.b, ∀ y ∈ relativeUnitFiltration S.1.chain S.1.b (i + 1),
      t * y * t⁻¹ ∈ relativeUnitFiltration S.1.chain S.1.b (i + 1) →
      elementCharacter (traceCharacter ψF) b (t * y * t⁻¹) =
        elementCharacter (traceCharacter ψF) b y := by
    intro t ht y hy hty
    have hyH : y ∈ simpleHGroup S.1.chain S.1.n S.1.b q.tail (i + 1) :=
      relativeUnitFiltration_le_simpleHGroup _ _ _ _ _ hy
    have htyH : t * y * t⁻¹ ∈ simpleHGroup S.1.chain S.1.n S.1.b q.tail (i + 1) :=
      relativeUnitFiltration_le_simpleHGroup _ _ _ _ _ hty
    rw [← hbχ ⟨_, htyH⟩, ← hbχ ⟨_, hyH⟩]
    congr 1
    have ht₀ : t ∈ characterSelfIntertwining φ₀ := hI₀ ▸ hBθ₀ ht
    have ht₁ := (Set.ext_iff.mp hIφ₀ t).mp ht₀
    obtain ⟨a', ha', c, hc, hac⟩ := Set.mem_mul.mp ht₁
    obtain ⟨a, ha, s, hs, rfl⟩ := Set.mem_mul.mp ha'
    have haN : a ∈ characterNormalizer θ₀ := hN₀ ▸ hYN ha
    have hcN : c ∈ characterNormalizer θ₀ := hN₀ ▸ hYN hc
    have haiN := inv_mem_characterNormalizer haN
    have haU : a ∈ S.1.chain.unitFiltration 1 := by
      have h₁ := hYU ha; rw [← hLTS]; exact h₁
    have hcU : c ∈ S.1.chain.unitFiltration 1 := by
      have h₁ := hYU hc; rw [← hLTS]; exact h₁
    have haiU : a⁻¹ ∈ S.1.chain.unitFiltration 1 := Subgroup.inv_mem _ haU
    obtain ⟨hcNH, hcθ⟩ := hnormS c (by rw [← hθres] at hcN; exact hcN)
    obtain ⟨haiNH, haiθ⟩ := hnormS a⁻¹ (by rw [← hθres] at haiN; exact haiN)
    have hwH : c * y * c⁻¹ ∈ simpleHGroup S.1.chain S.1.n S.1.b q.tail (i + 1) :=
      (Subgroup.mem_normalizer_iff.mp hcNH y).mp hyH
    have hw'H : a⁻¹ * (t * y * t⁻¹) * a⁻¹⁻¹ ∈
        simpleHGroup S.1.chain S.1.n S.1.b q.tail (i + 1) :=
      (Subgroup.mem_normalizer_iff.mp haiNH _).mp htyH
    have hsw : s * (c * y * c⁻¹) * s⁻¹ = a⁻¹ * (t * y * t⁻¹) * a⁻¹⁻¹ := by
      rw [← hac]; group
    have hsφS : s ∈ characterSelfIntertwining φS := by
      rw [characterSelfIntertwining_comp_inclusion hHm φ]; exact hBφ hs
    have e₁ := hsφS ⟨_, hwH⟩ (hsw ▸ hw'H)
    rw [character_congr φS hsw _ hw'H, hsplit, hsplit] at e₁
    have e₂ := haiθ _ htyH hw'H hty
    have e₃ := hcθ y hyH hwH hy
    have e₄ := (hBθ ht) ⟨y, hyH⟩ htyH
    have e₅ := hχconj a⁻¹ haiU haiNH _ htyH hw'H
    have e₆ := hχconj c hcU hcNH y hyH hwH
    change θ ⟨_, hw'H⟩ * χ ⟨_, hw'H⟩ = θ ⟨_, hwH⟩ * χ ⟨_, hwH⟩ at e₁
    refine mul_left_cancel (a := θ ⟨y, hyH⟩) ?_
    calc θ ⟨y, hyH⟩ * χ ⟨_, htyH⟩ = θ ⟨_, hw'H⟩ * χ ⟨_, hw'H⟩ :=
          congrArg₂ (· * ·) (e₂.trans e₄).symm e₅.symm
      _ = θ ⟨_, hwH⟩ * χ ⟨_, hwH⟩ := e₁
      _ = θ ⟨y, hyH⟩ * χ ⟨y, hyH⟩ := congrArg₂ (· * ·) e₃ e₆
  -- the refinement step gives the equivalent stratum
  obtain ⟨T', hT'c, hT'n, hT'r, hT's, hT'b⟩ :=
    simpleStratumIntertwinedRefinement F V ψF hψ S.1 (i + 1) hrS (by omega) hsS b hb hE2
  obtain ⟨q'', -, -⟩ := Stratum.exists_exact_definingSequenceChoice happrox T' hT's
  have hT'r0 : 0 ≤ T'.r := by rw [hT'r]; positivity
  have hdiff : T'.b - S.1.b ∈ S.1.chain.endFiltration (-((i + 1 : ℕ) : ℤ)) := by
    have h₁ : T'.b - (S.1.b + b) ∈ S.1.chain.endFiltration (-((i + 1 : ℕ) : ℤ)) :=
      S.1.chain.endFiltration_antitone (by push_cast; omega) hT'b
    have h₂ := add_mem h₁ hb
    rwa [show T'.b - (S.1.b + b) + b = T'.b - S.1.b by abel] at h₂
  -- change of the equivalent simple stratum at depth `i`
  obtain ⟨hHT', hCT'⟩ := (hchoice F V ψF hψ (S.1.atDepthZero (hr0S.trans_lt S.1.r_lt_n)) rfl hs₀
    (q.atDepthZero hr0S)).2 T' (by rw [hT'c]; rfl) hT'n hT's hT'r0 (by rw [hT'r]; exact hcS)
    (by rw [hT'r]; exact hdiff) q'' i (by rw [hT'r]; push_cast; omega) hiS hcS'
  have hHS' : simpleHGroup S.1.chain S.1.n S.1.b q.tail (i + 1) =
      simpleHGroup T'.chain T'.n T'.b q''.tail (i + 1) := hHT'
  have hH'T : simpleHGroup T'.chain T'.n T'.b q''.tail (i + 1) =
      simpleHGroup T.1.chain T.1.n T.1.b q'.tail (i + 1) := hHS'.symm.trans hHm
  let φ'' := φ.comp (Subgroup.inclusion hH'T.le)
  have hφ'' : φ'' ∈ simpleCharacters ψF T'.chain T'.n T'.b q''.tail i := by
    rw [hCT']
    refine ⟨θ, hθ, fun g => ?_⟩
    have hHS' : simpleHGroup S.1.chain S.1.n S.1.b q.tail (i + 1) =
        simpleHGroup T'.chain T'.n T'.b q''.tail (i + 1) := hHT'
    have hgS : (g : G) ∈ simpleHGroup S.1.chain S.1.n S.1.b q.tail (i + 1) := hHS'.ge g.2
    refine ⟨g.2, hgS, ?_⟩
    have e₁ : (φ'' ⟨g, g.2⟩ : ℂ) = (φS ⟨g, hgS⟩ : ℂ) := rfl
    have hgU : ((g : G) : A) - 1 ∈ S.1.chain.endFiltration ((i + 1 : ℕ) : ℤ) :=
      (simpleHGroup_le_unitFiltration _ _ _ _ _ hgS).2.2
    have e₂ : elementCharacter (traceCharacter ψF) (T'.b - (S.1.b + b)) g = 1 :=
      elementCharacter_eq_one_of_mem_endFiltration ψF hψ S.1.chain (by push_cast; omega) hT'b hgU
    have e₃ : elementCharacter (traceCharacter ψF) (T'.b - S.1.b) g =
        elementCharacter (traceCharacter ψF) b g := by
      rw [show T'.b - S.1.b = b + (T'.b - (S.1.b + b)) by abel, elementCharacter_add, e₂,
        mul_one]
    change (φ'' ⟨g, g.2⟩ : ℂ) = (θ ⟨g, hgS⟩ : ℂ) *
      elementCharacter (traceCharacter ψF) (T'.b - S.1.b) g
    rw [e₁, hsplit, Units.val_mul, hbχ, e₃]
  -- coherence at depth `i`
  have hiT'' : (i : ℤ) ≤ T'.r := by rw [hT'r]; push_cast; omega
  have hiT' : (i : ℤ) ≤ T.1.r := by rw [hrT]; push_cast; omega
  have hcohres := hcoh F V ψF hψ (T'.lowerIndex i hiT'') (T.1.lowerIndex i hiT') i
    (by change T.1.chain.order = T'.chain.order; rw [hT'c, hLTS])
    (by change T.1.n = T'.n; rw [hT'n, hnS, hnT]) rfl rfl (hT's.lowerIndex hiT'')
    (hsT.lowerIndex hiT') (q''.atIndex hiT'') (q'.atIndex hiT') hH'T
    (characterSet_ndrec_inter_nonempty hH'T hφ hφ'')
  have hcorr := characterSetTwistCorrespondence_of_ndrec_eq hH'T hcohres
  have hiT'n : (i : ℤ) < T'.n := by rw [hT'n]; exact hiS
  refine ⟨⟨T', hT'c.trans hLS, hT'n.trans hnS, hT'r, hT's⟩, ?_, ?_⟩
  · change T'.coset = S.1.coset
    unfold Stratum.coset
    rw [hT'c, hT'r, hrS]
    ext x
    simp only [Set.mem_ofPred_eq]
    constructor
    · intro hx
      have h₁ := add_mem hx hdiff
      rwa [show x - T'.b + (T'.b - S.1.b) = x - S.1.b by abel] at h₁
    · intro hx
      have h₁ := sub_mem hx hdiff
      rwa [show x - S.1.b - (T'.b - S.1.b) = x - T'.b by abel] at h₁
  · change simpleCharacterPairs ψF T' i = simpleCharacterPairs ψF T.1 i
    rw [simpleCharacterPairs_eq_image hchoice ψF hψ hT's hT'r0 q'' i hiT'n,
      simpleCharacterPairs_eq_image hchoice ψF hψ hsT hr0T q' i hiT]
    exact (characterPair_image_eq_iff _ _ ⟨φ'', hφ''⟩).mpr ⟨hH'T, hcorr⟩

/-- **BK93 (3.5.9) from published statements.** The published subgroup-property, restriction,
choice-independence, intertwining, commutator-pairing, coherence, conjugation-formula and
pure-stratum approximation statements imply `SimpleCharacterLoweringStatement`. -/
def SimpleCharacterLoweringReductionStatement : Prop :=
  SimpleStratumGroupPropertiesStatement.{uF, uV} → SimpleCharacterRestrictionStatement.{uF, uV} →
    SimpleCharacterChoiceStatement.{uF, uV} → SimpleCharacterIntertwiningStatement.{uF, uV} →
    SimpleCharacterPairingStatement.{uF, uV} → SimpleCharacterCoherenceStatement.{uF, uV} →
    SimpleCharacterCovarianceStatement.{uF, uV} →
    PureStratumSimpleApproximationStatement.{uF, uV} →
    SimpleCharacterLoweringStatement.{uF, uV}

theorem simpleCharacterLoweringReduction : SimpleCharacterLoweringReductionStatement.{uF, uV} := by
  intro hgroups hrestriction hchoice hint hpair hcoh hcov happrox F _ _ _ _ V _ _ _ ψF hψ
    L n m hm S T h
  have hnorm := simpleCharacterNormalizerRestrictionReduction hrestriction hint hcov
  refine ⟨simpleCharacterLoweringGroupsReduction hgroups hrestriction hchoice hint hpair F V ψF hψ
    L n m hm S T h, ?_⟩
  obtain ⟨i, rfl⟩ : ∃ i, m = i + 1 := ⟨m - 1, by omega⟩
  simp only [Nat.add_sub_cancel]
  by_cases hq : Nonempty S.1.DefiningSequenceChoice
  · obtain ⟨q⟩ := hq
    have hq' : Nonempty T.1.DefiningSequenceChoice := by
      by_contra hT
      have hr0S : 0 ≤ S.1.r := by rw [S.2.2.2.1]; positivity
      have hkS : ((i + 1 : ℕ) : ℤ) < S.1.n := by
        have := S.1.r_lt_n; rw [S.2.2.2.1] at this; exact this
      have hne := (hrestriction F V ψF hψ (S.1.atDepthZero (hr0S.trans_lt S.1.r_lt_n)) rfl
        (Stratum.isSimple_atDepthZero S.2.2.2.2 hr0S) (q.atDepthZero hr0S)).2.2.2.2 (i + 1) hkS
      rw [simpleCharacterPairs_eq_empty (not_nonempty_iff.mp hT),
        simpleCharacterPairs_eq_image hchoice ψF hψ S.2.2.2.2 hr0S q (i + 1) hkS] at h
      have he := Set.image_eq_empty.mp h
      have hne' : (simpleCharacters ψF S.1.chain S.1.n S.1.b q.tail (i + 1)).Nonempty := hne
      rw [he] at hne'
      exact Set.not_nonempty_empty hne'
    obtain ⟨q'⟩ := hq'
    exact exists_equivalent_simpleCharacterPairs_pred_eq hgroups hrestriction hchoice hint hpair
      hcoh hnorm happrox ψF hψ L n i S T h q q'
  · refine ⟨S, rfl, ?_⟩
    have hS : IsEmpty S.1.DefiningSequenceChoice := not_nonempty_iff.mp hq
    have hT : IsEmpty T.1.DefiningSequenceChoice := by
      by_contra hT
      obtain ⟨q'⟩ := not_isEmpty_iff.mp hT
      have hr0T : 0 ≤ T.1.r := by rw [T.2.2.2.1]; positivity
      have hkT : ((i + 1 : ℕ) : ℤ) < T.1.n := by
        have := T.1.r_lt_n; rw [T.2.2.2.1] at this; exact this
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
