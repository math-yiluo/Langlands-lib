import Langlands.BushnellKutzko.ClassCoverPremises
import Langlands.BushnellKutzko.SimpleCharacterTranslationStatement
import Langlands.BushnellKutzko.SimpleCharacterCoherenceStatement

/-! # Covering simple-character classes: the restriction fibres (BK94 (2.10)) -/

open ValuativeRel
open Langlands.Group.RelativeWeyl

noncomputable section

namespace Langlands.BushnellKutzko

universe uF uV uG

section Transport

variable {G : Type uG} [Group G]

/-- Equal pairs with characters in two sets give a common transported character. -/
theorem transport_inter_nonempty {H H' : Subgroup G} (C : Set (H →* ℂˣ)) (C' : Set (H' →* ℂˣ))
    {χ : H →* ℂˣ} {χ' : H' →* ℂˣ} (hχ : χ ∈ C) (hχ' : χ' ∈ C')
    (h : (⟨H, χ⟩ : CharacterPair G) = ⟨H', χ'⟩) :
    ∃ hH : H = H',
      (Eq.ndrec (motive := fun K : Subgroup G => Set (K →* ℂˣ)) C hH ∩ C').Nonempty := by
  obtain ⟨rfl, hh⟩ := Sigma.mk.inj_iff.mp h
  obtain rfl := eq_of_heq hh
  exact ⟨rfl, χ, hχ, hχ'⟩

/-- A character in a set that is carried to a second set gives an equal pair. -/
theorem exists_eq_pair_of_transport {H H' : Subgroup G} (C : Set (H →* ℂˣ))
    (C' : Set (H' →* ℂˣ)) (hH : H = H')
    (hC : Eq.ndrec (motive := fun K : Subgroup G => Set (K →* ℂˣ)) C hH = C')
    {χ : H →* ℂˣ} (hχ : χ ∈ C) :
    ∃ χ' ∈ C', (⟨H, χ⟩ : CharacterPair G) = ⟨H', χ'⟩ := by
  subst hH
  subst hC
  exact ⟨χ, hχ, rfl⟩

end Transport

variable {F : Type uF} [Field F] [ValuativeRel F] [TopologicalSpace F]
  [IsNonarchimedeanLocalField F] {V : Type uV} [AddCommGroup V] [Module F V]

local notation "A" => Module.End F V
local notation "G" => (Module.End F V)ˣ

variable (ψF : AddChar F ℂ)

/-- **BK93 (3.3.20)** for pairs: one defining sequence computes all of `Ĉ(𝔄,j,β)`, for every
`j ≤ r`. -/
theorem simpleCharacterPairs_eq_choiceImage_of_le (hChoice : SimpleCharacterChoiceStatement.{uF, uV})
    (hψ : IsBKAdditiveCharacter ψF) (T : Stratum 𝒪[F] F V) (j : ℕ) (hTr : (j : ℤ) ≤ T.r)
    (hT : T.IsSimple) (q₀ : T.DefiningSequenceChoice) :
    simpleCharacterPairs ψF T j =
      (fun θ => (⟨simpleHGroup T.chain T.n T.b q₀.tail (j + 1), θ⟩ : CharacterPair G)) ''
        simpleCharacters ψF T.chain T.n T.b q₀.tail j := by
  apply Set.Subset.antisymm
  · intro P hP
    simp only [simpleCharacterPairs, Set.mem_iUnion, Set.mem_image] at hP
    obtain ⟨q, θ, hθ, rfl⟩ := hP
    have h0 : (0 : ℤ) ≤ T.r := by omega
    obtain ⟨hq, -⟩ := hChoice F V ψF hψ (T.atDepthZero (h0.trans_lt T.r_lt_n)) rfl
      (Stratum.isSimple_atDepthZero hT h0) (q₀.atDepthZero h0)
    obtain ⟨hH, hC⟩ := hq (q.atDepthZero h0) j
      (by have := T.r_lt_n; change (j : ℤ) < T.n; omega)
    change simpleHGroup T.chain T.n T.b q₀.tail (j + 1) =
      simpleHGroup T.chain T.n T.b q.tail (j + 1) at hH
    change simpleCharacters ψF T.chain T.n T.b q.tail j =
      characterSetTwist _ (simpleCharacters ψF T.chain T.n T.b q₀.tail j) (fun _ => 1) at hC
    rw [hC] at hθ
    obtain ⟨θ₀, hθ₀, hagree⟩ := hθ
    refine ⟨θ₀, hθ₀, CharacterPair.ext_of_eq hH (fun g hP hQ => ?_)⟩
    obtain ⟨h₁, h₂, h⟩ := hagree ⟨g, hQ⟩
    exact Units.ext (by simpa using h.symm)
  · rintro P ⟨θ, hθ, rfl⟩
    exact Set.mem_iUnion.mpr ⟨q₀, θ, hθ, rfl⟩

/-- **BK93 (3.3.20)** for pairs: one defining sequence computes all of `Ĉ(𝔄,j,β)`. -/
theorem simpleCharacterPairs_eq_choiceImage (hChoice : SimpleCharacterChoiceStatement.{uF, uV})
    (hψ : IsBKAdditiveCharacter ψF) (T : Stratum 𝒪[F] F V) (j : ℕ) (hTr : T.r = j)
    (hT : T.IsSimple) (q₀ : T.DefiningSequenceChoice) :
    simpleCharacterPairs ψF T j =
      (fun θ => (⟨simpleHGroup T.chain T.n T.b q₀.tail (j + 1), θ⟩ : CharacterPair G)) ''
        simpleCharacters ψF T.chain T.n T.b q₀.tail j :=
  simpleCharacterPairs_eq_choiceImage_of_le ψF hChoice hψ T j hTr.ge hT q₀

/-- **BK93 (3.5.8)** for pairs: a common pair forces the second set of pairs to contain
the first. -/
theorem simpleCharacterPairs_subset_of_common
    (hChoice : SimpleCharacterChoiceStatement.{uF, uV})
    (hCoh : SimpleCharacterCoherenceStatement.{uF, uV}) (hψ : IsBKAdditiveCharacter ψF)
    (T₁ T₂ : Stratum 𝒪[F] F V) (j : ℕ) (hr₁ : T₁.r = j) (hr₂ : T₂.r = j) (h₁ : T₁.IsSimple)
    (h₂ : T₂.IsSimple) (horder : T₂.chain.order = T₁.chain.order) (hn : T₂.n = T₁.n)
    {P : CharacterPair G} (hP₁ : P ∈ simpleCharacterPairs ψF T₁ j)
    (hP₂ : P ∈ simpleCharacterPairs ψF T₂ j) :
    simpleCharacterPairs ψF T₁ j ⊆ simpleCharacterPairs ψF T₂ j := by
  simp only [simpleCharacterPairs, Set.mem_iUnion, Set.mem_image] at hP₁ hP₂
  obtain ⟨q₁, χ₁, hχ₁, rfl⟩ := hP₁
  obtain ⟨q₂, χ₂, hχ₂, heq⟩ := hP₂
  obtain ⟨hH, hne⟩ := transport_inter_nonempty _ _ hχ₁ hχ₂ heq.symm
  have hC := hCoh F V ψF hψ T₁ T₂ j horder hn hr₁ hr₂ h₁ h₂ q₁ q₂ hH hne
  rw [simpleCharacterPairs_eq_choiceImage ψF hChoice hψ T₁ j hr₁ h₁ q₁,
    simpleCharacterPairs_eq_choiceImage ψF hChoice hψ T₂ j hr₂ h₂ q₂]
  rintro P ⟨χ, hχ, rfl⟩
  obtain ⟨χ', hχ', hpair⟩ := exists_eq_pair_of_transport _ _ hH hC hχ
  exact ⟨χ', hχ', hpair.symm⟩

/-- A conjugate of a simple stratum by `U(𝔄)` is a simple stratum on the same chain. -/
theorem exists_conj_simpleStratumAt [FiniteDimensional F V]
    (hConj : SimpleCharacterConjugationStatement.{uF, uV}) (hψ : IsBKAdditiveCharacter ψF)
    (L : LatticeChain 𝒪[F] F V) (n : ℤ) (k : ℕ) (S : SimpleStratumAt L n k) {u : G}
    (hu : u ∈ L.unitFiltration 0) :
    ∃ S' : SimpleStratumAt L n k, S'.1.b = (↑u⁻¹ : A) * S.1.b * (u : A) := by
  obtain ⟨hSL, hSn, hSr, hS⟩ := S.2
  obtain ⟨-, -, -, -, T', hT'chain, hT'n, hT'r, hT'b, hT'simple, -, -, -, -⟩ :=
    hConj F V ψF hψ S.1 k hSr hS u⁻¹
  have hL' : T'.chain = L := by
    rw [hT'chain, hSL]
    exact L.linearEquivMap_unit (inv_mem hu)
  refine ⟨⟨T', hL', hT'n.trans hSn, hT'r.trans hSr, hT'simple⟩, ?_⟩
  rw [hT'b]
  ext v
  rfl

/-- **BK94 (2.10).** Let `V` be finite-dimensional, `k + 1 < n`, `[𝔄,n,k+1,γ]` a simple stratum
on `L` and `θ ∈ Ĉ(𝔄,k+1,γ)`. A pair of `S^k_n(𝔄)` whose restriction to `U^{k+2}(𝔄)` is
`U(𝔄)`-conjugate to `θ` is `U(𝔄)`-conjugate to a pair of `Ĉ(𝔄,k,β)`, for a simple stratum
`[𝔄,n,k,β]` on `L` with `β ≡ γ (mod 𝔓^{-(k+1)})`, whose restriction to `U^{k+2}(𝔄)` is `θ`. -/
theorem exists_fibre_representative [FiniteDimensional F V]
    (hApprox : PureStratumSimpleApproximationStatement.{uF, uV})
    (hConj : SimpleCharacterConjugationStatement.{uF, uV})
    (hChoice : SimpleCharacterChoiceStatement.{uF, uV})
    (hGroups : SimpleStratumGroupPropertiesStatement.{uF, uV})
    (hRestr : SimpleCharacterRestrictionStatement.{uF, uV})
    (hCoh : SimpleCharacterCoherenceStatement.{uF, uV})
    (hTransl : SimpleCharacterTranslationStatement.{uF, uV}) (hψ : IsBKAdditiveCharacter ψF)
    (L : LatticeChain 𝒪[F] F V) (n : ℤ) (k : ℕ) (hk : (k : ℤ) + 1 < n)
    (T : SimpleStratumAt L n ((k + 1 : ℕ) : ℤ)) {θ : CharacterPair G}
    (hθ : θ ∈ simpleCharacterPairs ψF T.1 (k + 1)) {P : CharacterPair G}
    (hP : P ∈ simpleCharacterPairsAt ψF L n k)
    (hPθ : CharacterPair.AreConjugateBy (L.unitFiltration 0)
      (P.restrict (L.unitFiltration (k + 2))) θ) :
    ∃ S : SimpleStratumAt L n k, S.1.b - T.1.b ∈ L.endFiltration (-((k + 1 : ℕ) : ℤ)) ∧
      ∃ P₁ ∈ simpleCharacterPairs ψF S.1 k,
        CharacterPair.AreConjugateBy (L.unitFiltration 0) P P₁ ∧
        P₁.restrict (L.unitFiltration (k + 2)) = θ := by
  obtain ⟨S₁, hPS₁⟩ := Set.mem_iUnion.mp hP
  obtain ⟨⟨x, hx⟩, hxθ⟩ := hPθ
  obtain ⟨S₁', hS₁'⟩ := exists_conj_simpleStratumAt ψF hConj hψ L n k S₁ hx
  have hP₁ : P.conj x ∈ simpleCharacterPairs ψF S₁'.1 k :=
    simpleCharacterPairs_conj_mem ψF hApprox hConj hChoice hψ L n k S₁ S₁' x hx
      (by rw [hS₁', sub_self]; exact zero_mem _) P hPS₁
  have hres : (P.conj x).restrict (L.unitFiltration (k + 2)) = θ := by
    rw [CharacterPair.restrict_conj P _ x (L.conj_mem_unitFiltration_iff hx (k + 2))]
    exact hxθ
  obtain ⟨T₁, hT₁b, hT₁⟩ :=
    exists_restrict_mem_succ ψF hGroups hRestr hψ L n k hk S₁' (P.conj x) hP₁
  rw [hres] at hT₁
  obtain ⟨hT₁L, hT₁n, hT₁r, hT₁s⟩ := T₁.2
  obtain ⟨hTL, hTn, hTr, hTs⟩ := T.2
  have hCeq : simpleCharacterPairs ψF T₁.1 (k + 1) = simpleCharacterPairs ψF T.1 (k + 1) :=
    Set.Subset.antisymm
      (simpleCharacterPairs_subset_of_common ψF hChoice hCoh hψ T₁.1 T.1 (k + 1) hT₁r hTr hT₁s
        hTs (by rw [hTL, hT₁L]) (hTn.trans hT₁n.symm) hT₁ hθ)
      (simpleCharacterPairs_subset_of_common ψF hChoice hCoh hψ T.1 T₁.1 (k + 1) hTr hT₁r hTs
        hT₁s (by rw [hTL, hT₁L]) (hT₁n.trans hTn.symm) hθ hT₁)
  have hcast : ∀ U : SimpleStratumAt L n ((k + 1 : ℕ) : ℤ), U.1.r = (k : ℤ) + 1 := fun U => by
    rw [U.2.2.2.1]
    push_cast
    rfl
  obtain ⟨S₂, hS₂b, hS₂C⟩ := hTransl F V ψF hψ L n k hk
    ⟨T₁.1, hT₁L, hT₁n, hcast T₁, hT₁s⟩ ⟨T.1, hTL, hTn, hcast T, hTs⟩ S₁' hCeq
    (by
      have := neg_mem hT₁b
      rw [neg_sub] at this
      simpa using this)
  refine ⟨S₂, by simpa using hS₂b, P.conj x, ?_, ⟨⟨x, hx⟩, rfl⟩, hres⟩
  rw [hS₂C]
  exact hP₁

/-- The set `Y(θ)` of BK94 p. 120, for a simple stratum `[𝔄,n,k+1,γ]` on `L`: the pairs of the
sets `Ĉ(𝔄,k,β)`, over simple strata `[𝔄,n,k,β]` on `L` with `β ≡ γ (mod 𝔓^{-(k+1)})`, whose
restriction to `U^{k+2}(𝔄)` is `θ`. -/
def fibrePairs (L : LatticeChain 𝒪[F] F V) (n : ℤ) (k : ℕ)
    (T : SimpleStratumAt L n ((k + 1 : ℕ) : ℤ)) (θ : CharacterPair G) : Set (CharacterPair G) :=
  {P | ∃ S : SimpleStratumAt L n k, S.1.b - T.1.b ∈ L.endFiltration (-((k + 1 : ℕ) : ℤ)) ∧
    P ∈ simpleCharacterPairs ψF S.1 k ∧ P.restrict (L.unitFiltration (k + 2)) = θ}

/-- **BK94 (2.9), upper half.** For each simple stratum `[𝔄,n,k+1,γ]` on `L` and each
`θ ∈ Ĉ(𝔄,k+1,γ)`, there is a choice, for each pair `P` of `Y(θ)`, of a simple stratum
`[𝔄,n,k,β]` on `L` with `β ≡ γ (mod 𝔓^{-(k+1)})` carrying a `U(𝔄)`-conjugate of `P`, such that
strata related by `unitConjCongr` are chosen only for `U(𝔄)`-conjugate pairs. -/
def FibreClassInjectionAt (L : LatticeChain 𝒪[F] F V) (n : ℤ) (k : ℕ) : Prop :=
  ∀ (T : SimpleStratumAt L n ((k + 1 : ℕ) : ℤ)) (θ : CharacterPair G),
    θ ∈ simpleCharacterPairs ψF T.1 (k + 1) →
    ∃ κ : fibrePairs ψF L n k T θ → SimpleStratumAt L n k,
      ∀ P, (κ P).1.b - T.1.b ∈ L.endFiltration (-((k + 1 : ℕ) : ℤ)) ∧
        (∃ P' ∈ simpleCharacterPairs ψF (κ P).1 k,
          CharacterPair.AreConjugateBy (L.unitFiltration 0) P.1 P') ∧
        ∀ Q, unitConjCongr L k (κ P).1.b (κ Q).1.b →
          CharacterPair.AreConjugateBy (L.unitFiltration 0) P.1 Q.1

/-- The fibre injection from the injection on `Y(θ)` and BK94 (2.10). -/
theorem fibreInjectionAt_of_fibreClassInjection [FiniteDimensional F V]
    (hApprox : PureStratumSimpleApproximationStatement.{uF, uV})
    (hConj : SimpleCharacterConjugationStatement.{uF, uV})
    (hChoice : SimpleCharacterChoiceStatement.{uF, uV})
    (hGroups : SimpleStratumGroupPropertiesStatement.{uF, uV})
    (hRestr : SimpleCharacterRestrictionStatement.{uF, uV})
    (hCoh : SimpleCharacterCoherenceStatement.{uF, uV})
    (hTransl : SimpleCharacterTranslationStatement.{uF, uV}) (hψ : IsBKAdditiveCharacter ψF)
    (L : LatticeChain 𝒪[F] F V) (n : ℤ) (k : ℕ) (hk : (k : ℤ) + 1 < n)
    (hY : FibreClassInjectionAt ψF L n k) : FibreInjectionAt ψF L n k := by
  intro T θ hθ
  obtain ⟨κ₀, hκ₀⟩ := hY T θ hθ
  have hrep : ∀ P : simpleCharacterPairsAt ψF L n k, ∃ P₁ : CharacterPair G,
      CharacterPair.AreConjugateBy (L.unitFiltration 0)
          (P.1.restrict (L.unitFiltration (k + 2))) θ →
        P₁ ∈ fibrePairs ψF L n k T θ ∧ CharacterPair.AreConjugateBy (L.unitFiltration 0) P.1 P₁ := by
    intro P
    by_cases h : CharacterPair.AreConjugateBy (L.unitFiltration 0)
        (P.1.restrict (L.unitFiltration (k + 2))) θ
    · obtain ⟨S, hSb, P₁, hP₁, hPP₁, hres⟩ := exists_fibre_representative ψF hApprox hConj hChoice
        hGroups hRestr hCoh hTransl hψ L n k hk T hθ P.2 h
      exact ⟨P₁, fun _ => ⟨⟨S, hSb, hP₁, hres⟩, hPP₁⟩⟩
    · exact ⟨θ, fun h' => (h h').elim⟩
  choose rep hrep using hrep
  have hS : ∀ P : simpleCharacterPairsAt ψF L n k, ∃ S : SimpleStratumAt L n k,
      P.1 ∈ simpleCharacterPairs ψF S.1 k := fun P => Set.mem_iUnion.mp P.2
  choose stratumOf _ using hS
  classical
  refine ⟨fun P => if h : CharacterPair.AreConjugateBy (L.unitFiltration 0)
      (P.1.restrict (L.unitFiltration (k + 2))) θ then κ₀ ⟨rep P, (hrep P h).1⟩ else stratumOf P,
    fun P hP => ?_⟩
  simp only [dite_eq_left hP]
  obtain ⟨hb, ⟨P', hP', hc⟩, hinj⟩ := hκ₀ ⟨rep P, (hrep P hP).1⟩
  refine ⟨hb, ⟨P', hP', (hrep P hP).2.trans hc⟩, fun Q hQ hPQ => ?_⟩
  simp only [dite_eq_left hQ] at hPQ
  exact ((hrep P hP).2.trans (hinj _ hPQ)).trans (hrep Q hQ).2.symm

/-- **BK93 (3.3.21)** for pairs: every pair of `Ĉ(𝔄,k+1,γ)` is the restriction of a pair of
`Ĉ(𝔄,k,γ)`. -/
theorem exists_pair_restrict_eq (hGroups : SimpleStratumGroupPropertiesStatement.{uF, uV})
    (hRestr : SimpleCharacterRestrictionStatement.{uF, uV}) (hψ : IsBKAdditiveCharacter ψF)
    (T : Stratum 𝒪[F] F V) (k : ℕ) (hTr : T.r = ((k + 1 : ℕ) : ℤ)) (hT : T.IsSimple)
    {θ : CharacterPair G} (hθ : θ ∈ simpleCharacterPairs ψF T (k + 1)) :
    ∃ ϑ ∈ simpleCharacterPairs ψF T k, ϑ.restrict (T.chain.unitFiltration (k + 2)) = θ := by
  simp only [simpleCharacterPairs, Set.mem_iUnion, Set.mem_image] at hθ
  obtain ⟨q, θ', hθ', rfl⟩ := hθ
  have h0 : (0 : ℤ) ≤ T.r := by omega
  have hT0 := Stratum.isSimple_atDepthZero hT h0
  obtain ⟨hcarrier, -⟩ := hGroups F V (T.atDepthZero (h0.trans_lt T.r_lt_n)) rfl hT0
    (q.atDepthZero h0)
  obtain ⟨-, -, -, hd, -⟩ := hRestr F V ψF hψ (T.atDepthZero (h0.trans_lt T.r_lt_n)) rfl hT0
    (q.atDepthZero h0)
  have h : simpleCharacterRestriction (T.atDepthZero (h0.trans_lt T.r_lt_n)) (q.atDepthZero h0)
      (Nat.le_succ k) '' simpleCharacters ψF T.chain T.n T.b q.tail k =
      simpleCharacters ψF T.chain T.n T.b q.tail (k + 1) :=
    hd k (by have := T.r_lt_n; change (k : ℤ) + 1 < T.n; push_cast at hTr; omega)
  rw [← h] at hθ'
  obtain ⟨χ, hχ, rfl⟩ := hθ'
  refine ⟨⟨_, χ⟩, Set.mem_iUnion.mpr ⟨q, χ, hχ, rfl⟩, ?_⟩
  have hdom : simpleHGroup T.chain T.n T.b q.tail (k + 1) ⊓ T.chain.unitFiltration (k + 2) =
      simpleHGroup T.chain T.n T.b q.tail (k + 2) := by
    ext g
    have h1 : (simpleHGroup T.chain T.n T.b q.tail (k + 1) : Set G) =
        simpleHCarrier T.chain T.n T.b q.tail (k + 1) := (hcarrier (k + 1)).1
    have h2 : (simpleHGroup T.chain T.n T.b q.tail (k + 2) : Set G) =
        simpleHCarrier T.chain T.n T.b q.tail (k + 2) := (hcarrier (k + 2)).1
    rw [Subgroup.mem_inf, ← SetLike.mem_coe, h1,
      ← SetLike.mem_coe (p := simpleHGroup T.chain T.n T.b q.tail (k + 2)), h2]
    simp only [simpleHCarrier, Set.mem_ofPred_eq]
    constructor
    · rintro ⟨⟨-, hg⟩, hg2⟩
      exact ⟨hg2, hg⟩
    · rintro ⟨hg2, hg⟩
      exact ⟨⟨T.chain.unitFiltration_antitone (by omega) hg2, hg⟩, hg2⟩
  exact CharacterPair.ext_of_eq hdom (fun g hP hQ => rfl)

/-- **BK94 (2.8), (ii) ⇒ (iii), for the twist coefficients `c_i = β_i - γ`.** Let
`[𝔄,n,k+1,γ]` be a simple stratum on `L` and `ϑ ∈ Ĉ(𝔄,k,γ)`. Let `[𝔄,n,k,β_i]` (`i = 1, 2`) be
simple strata on `L` with `β_i ≡ γ (mod 𝔓^{-(k+1)})`, and `P_i ∈ Ĉ(𝔄,k,β_i)` pairs on the
subgroup of `ϑ` whose characters
are `ϑ ψ_{β_i-γ}`. If `β₂ ≡ u⁻¹ β₁ u (mod 𝔓^{-k})` for some `u ∈ U(𝔄)`, then `P₁` and `P₂` are
`U(𝔄)`-conjugate. -/
def TwistConjugacyAt (L : LatticeChain 𝒪[F] F V) (n : ℤ) (k : ℕ) : Prop :=
  ∀ (T : SimpleStratumAt L n ((k + 1 : ℕ) : ℤ)) (ϑ : CharacterPair G),
    ϑ ∈ simpleCharacterPairs ψF T.1 k →
    ∀ (S₁ S₂ : SimpleStratumAt L n k) (P₁ P₂ : CharacterPair G),
      S₁.1.b - T.1.b ∈ L.endFiltration (-((k + 1 : ℕ) : ℤ)) →
      S₂.1.b - T.1.b ∈ L.endFiltration (-((k + 1 : ℕ) : ℤ)) →
      P₁ ∈ simpleCharacterPairs ψF S₁.1 k → P₂ ∈ simpleCharacterPairs ψF S₂.1 k →
      P₁.1 = ϑ.1 → P₂.1 = ϑ.1 →
      characterAgreesOn ϑ.1 P₁.2 ϑ.2 (elementCharacter (traceCharacter ψF) (S₁.1.b - T.1.b)) →
      characterAgreesOn ϑ.1 P₂.2 ϑ.2 (elementCharacter (traceCharacter ψF) (S₂.1.b - T.1.b)) →
      unitConjCongr L k S₁.1.b S₂.1.b →
      CharacterPair.AreConjugateBy (L.unitFiltration 0) P₁ P₂

/-- **BK94 (2.7) and (1.8).** Let `[𝔄,n,k+1,γ]` be a simple stratum on `L` and fix
`ϑ ∈ Ĉ(𝔄,k,γ)`, with restriction `θ` to `U^{k+2}(𝔄)`. Every pair of `Y(θ)` is `U(𝔄)`-conjugate
to a pair of `Ĉ(𝔄,k,β)` on the subgroup of `ϑ` whose character is `ϑ ψ_{β-γ}`, for some simple
stratum `[𝔄,n,k,β]` on `L` with `β ≡ γ (mod 𝔓^{-(k+1)})`. -/
def FibreTwistCoverAt (L : LatticeChain 𝒪[F] F V) (n : ℤ) (k : ℕ) : Prop :=
  ∀ (T : SimpleStratumAt L n ((k + 1 : ℕ) : ℤ)) (ϑ : CharacterPair G),
    ϑ ∈ simpleCharacterPairs ψF T.1 k →
    ∀ P ∈ fibrePairs ψF L n k T (ϑ.restrict (L.unitFiltration (k + 2))),
      ∃ S : SimpleStratumAt L n k, S.1.b - T.1.b ∈ L.endFiltration (-((k + 1 : ℕ) : ℤ)) ∧
        ∃ P' ∈ simpleCharacterPairs ψF S.1 k, P'.1 = ϑ.1 ∧
          characterAgreesOn ϑ.1 P'.2 ϑ.2 (elementCharacter (traceCharacter ψF) (S.1.b - T.1.b)) ∧
          CharacterPair.AreConjugateBy (L.unitFiltration 0) P P'

/-- **BK94 (2.9), upper half,** from (2.7)–(2.8). -/
theorem fibreClassInjectionAt_of_twist (hGroups : SimpleStratumGroupPropertiesStatement.{uF, uV})
    (hRestr : SimpleCharacterRestrictionStatement.{uF, uV}) (hψ : IsBKAdditiveCharacter ψF)
    (L : LatticeChain 𝒪[F] F V) (n : ℤ) (k : ℕ) (hconj : TwistConjugacyAt ψF L n k)
    (hcover : FibreTwistCoverAt ψF L n k) : FibreClassInjectionAt ψF L n k := by
  intro T θ hθ
  obtain ⟨hTL, hTn, hTr, hTs⟩ := T.2
  obtain ⟨ϑ, hϑ, hres⟩ := exists_pair_restrict_eq ψF hGroups hRestr hψ T.1 k hTr hTs hθ
  rw [hTL] at hres
  have hcov : ∀ P : fibrePairs ψF L n k T θ, ∃ S : SimpleStratumAt L n k,
      S.1.b - T.1.b ∈ L.endFiltration (-((k + 1 : ℕ) : ℤ)) ∧
        ∃ P' ∈ simpleCharacterPairs ψF S.1 k, P'.1 = ϑ.1 ∧
          characterAgreesOn ϑ.1 P'.2 ϑ.2 (elementCharacter (traceCharacter ψF) (S.1.b - T.1.b)) ∧
          CharacterPair.AreConjugateBy (L.unitFiltration 0) P.1 P' := by
    intro P
    have hP : P.1 ∈ fibrePairs ψF L n k T (ϑ.restrict (L.unitFiltration (k + 2))) := by
      rw [hres]
      exact P.2
    exact hcover T ϑ hϑ P.1 hP
  choose κ hκb P' hP' hP'1 hP'2 hPP' using hcov
  refine ⟨κ, fun P => ⟨hκb P, ⟨P' P, hP' P, hPP' P⟩, fun Q hPQ => ?_⟩⟩
  exact (hPP' P).trans ((hconj T ϑ hϑ (κ P) (κ Q) (P' P) (P' Q) (hκb P) (hκb Q) (hP' P)
    (hP' Q) (hP'1 P) (hP'1 Q) (hP'2 P) (hP'2 Q) hPQ).trans (hPP' Q).symm)

end Langlands.BushnellKutzko
