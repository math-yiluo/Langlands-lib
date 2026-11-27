import Langlands.BushnellKutzko.ClassCoverSurj

/-! # Covering simple-character classes: twisting by `ψ_{β-γ}` (BK93 (3.3.18), (3.3.20)) -/

open ValuativeRel

noncomputable section

namespace Langlands.BushnellKutzko

universe uF uV

variable {F : Type uF} [Field F] [ValuativeRel F] [TopologicalSpace F]
  [IsNonarchimedeanLocalField F] {V : Type uV} [AddCommGroup V] [Module F V]

local notation "A" => Module.End F V
local notation "G" => (Module.End F V)ˣ

omit [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F] in
theorem elementCharacter_neg_mul_self (ψF : AddChar F ℂ) (b : A) (g : G) :
    elementCharacter (traceCharacter ψF) (-b) g * elementCharacter (traceCharacter ψF) b g = 1 := by
  rw [← elementCharacter_add, neg_add_cancel]
  simp [elementCharacter_apply]

variable (ψF : AddChar F ℂ)

/-- **BK93 (3.3.18), (3.3.20)(ii).** Let `ψ_F` be trivial on `𝔭_F` and nontrivial on `𝔬_F`, and
let `[𝔄,n,k+1,γ]` and `[𝔄,n,k,β]` both be simple strata on the same indexed lattice chain with
`β ≡ γ (mod 𝔓^{-(k+1)})`. For any choices of defining sequences, the two groups at index `k + 1`
coincide, and the simple characters of `β` at index `k` are exactly the products of those of `γ`
with `ψ_{β-γ}`. -/
theorem twist_correspondence (hChoice : SimpleCharacterChoiceStatement.{uF, uV})
    (hRestr : SimpleCharacterRestrictionStatement.{uF, uV}) (hψ : IsBKAdditiveCharacter ψF)
    (k : ℕ) (T S : Stratum 𝒪[F] F V) (hTchain : T.chain = S.chain) (hTn : T.n = S.n)
    (hTr : T.r = ((k + 1 : ℕ) : ℤ)) (hSr : S.r = k) (hTs : T.IsSimple) (hSs : S.IsSimple)
    (hb : S.b - T.b ∈ S.chain.endFiltration (-((k + 1 : ℕ) : ℤ)))
    (q : S.DefiningSequenceChoice) (qT : T.DefiningSequenceChoice) :
    simpleHGroup S.chain S.n S.b q.tail (k + 1) = simpleHGroup T.chain T.n T.b qT.tail (k + 1) ∧
      (∀ θ ∈ simpleCharacters ψF S.chain S.n S.b q.tail k,
        ∃ χ ∈ simpleCharacters ψF T.chain T.n T.b qT.tail k,
          ∀ (g : G) (h₁ : g ∈ simpleHGroup S.chain S.n S.b q.tail (k + 1))
            (h₂ : g ∈ simpleHGroup T.chain T.n T.b qT.tail (k + 1)),
            (θ ⟨g, h₁⟩ : ℂ) = χ ⟨g, h₂⟩ * elementCharacter (traceCharacter ψF) (S.b - T.b) g) ∧
      (∀ χ ∈ simpleCharacters ψF T.chain T.n T.b qT.tail k,
        ∃ θ ∈ simpleCharacters ψF S.chain S.n S.b q.tail k,
          ∀ (g : G) (h₁ : g ∈ simpleHGroup S.chain S.n S.b q.tail (k + 1))
            (h₂ : g ∈ simpleHGroup T.chain T.n T.b qT.tail (k + 1)),
            (θ ⟨g, h₁⟩ : ℂ) = χ ⟨g, h₂⟩ * elementCharacter (traceCharacter ψF) (S.b - T.b) g) := by
  have h0 : (0 : ℤ) ≤ S.r := by rw [hSr]; positivity
  have hS0 := Stratum.isSimple_atDepthZero hSs h0
  have hbT : T.b - S.b ∈ S.chain.endFiltration (-T.r) := by
    rw [hTr, ← neg_sub]
    exact neg_mem hb
  have hTU : simpleHGroup T.chain T.n T.b qT.tail (k + 1) ≤ S.chain.unitFiltration (k + 1) := by
    exact (simpleHGroup_le_unitFiltration T.chain T.n T.b qT.tail (k + 1)).trans
      (le_of_eq (congrArg (fun M : LatticeChain 𝒪[F] F V => M.unitFiltration (k + 1)) hTchain))
  have hcancel : ∀ g : G, elementCharacter (traceCharacter ψF) (T.b - S.b) g *
      elementCharacter (traceCharacter ψF) (S.b - T.b) g = 1 := fun g => by
    rw [← neg_sub]
    exact elementCharacter_neg_mul_self ψF _ g
  have hne : ∀ g : G, elementCharacter (traceCharacter ψF) (S.b - T.b) g ≠ 0 := fun g h => by
    have := hcancel g
    rw [h, mul_zero] at this
    exact zero_ne_one this
  have horder : T.chain.order = (S.atDepthZero (h0.trans_lt S.r_lt_n)).chain.order := by
    rw [hTchain]
    rfl
  by_cases hcrit : criticalExponent S.chain S.b < ((-((k + 1 : ℕ) : ℤ) : ℤ) : WithBot ℤ)
  · -- `[𝔄,n,k+1,β]` is simple: the twist clause of BK93 (3.3.20)
    let S₁ : Stratum 𝒪[F] F V :=
      { S with r := ((k + 1 : ℕ) : ℤ), r_lt_n := by rw [← hTr, ← hTn]; exact T.r_lt_n }
    have hS₁ : S₁.IsSimple := ⟨hSs.1, hcrit⟩
    have hdepth : ((k + 1 : ℕ) : ℤ) < simpleCriticalDepth S.chain S.b :=
      hS₁.r_lt_simpleCriticalDepth
    obtain ⟨hH, hC⟩ := (hChoice F V ψF hψ (S.atDepthZero (h0.trans_lt S.r_lt_n)) rfl hS0
      (q.atDepthZero h0)).2 T horder (hTn.trans rfl) hTs
      (by rw [hTr]; positivity) (by rw [hTr]; exact hdepth) hbT qT k
      (by rw [hTr]; push_cast; omega) (by have := S.r_lt_n; change (k : ℤ) < S.n; omega)
      (lt_of_le_of_lt (WithTop.coe_le_coe.mpr (by push_cast; omega)) hdepth)
    change simpleHGroup S.chain S.n S.b q.tail (k + 1) =
      simpleHGroup T.chain T.n T.b qT.tail (k + 1) at hH
    change simpleCharacters ψF T.chain T.n T.b qT.tail k =
      characterSetTwist _ (simpleCharacters ψF S.chain S.n S.b q.tail k)
        (elementCharacter (traceCharacter ψF) (T.b - S.b)) at hC
    refine ⟨hH, fun θ hθ => ?_, fun χ hχ => ?_⟩
    · have hbT' : T.b - S.b ∈ S.chain.endFiltration (-((k + 1 : ℕ) : ℤ)) := by
        rw [← hTr]
        exact hbT
      let ψh := elementCharacterHom S.chain ψF hψ hbT' (k := k + 1)
        (show 1 ≤ -((k + 1 : ℕ) : ℤ) + (((k + 1 : ℕ) : ℤ) + ((k + 1 : ℕ) : ℤ)) by push_cast; omega)
        hTU
      let χ := θ.comp (MulEquiv.subgroupCongr hH.symm).toMonoidHom * ψh
      have hχ : χ ∈ simpleCharacters ψF T.chain T.n T.b qT.tail k := by
        rw [hC]
        refine ⟨θ, hθ, fun g => ⟨g.2, (congrArg (fun K : Subgroup G => (g : G) ∈ K) hH).mpr g.2, ?_⟩⟩
        rfl
      refine ⟨χ, hχ, fun g h₁ h₂ => ?_⟩
      change (θ ⟨g, h₁⟩ : ℂ) = (θ ⟨g, _⟩ : ℂ) * elementCharacter (traceCharacter ψF)
        (T.b - S.b) g * elementCharacter (traceCharacter ψF) (S.b - T.b) g
      rw [mul_assoc, hcancel, mul_one]
    · rw [hC] at hχ
      obtain ⟨θ, hθ, hag⟩ := hχ
      refine ⟨θ, hθ, fun g h₁ h₂ => ?_⟩
      obtain ⟨m₁, m₂, e⟩ := hag ⟨g, h₂⟩
      change (χ ⟨g, m₁⟩ : ℂ) = (θ ⟨g, m₂⟩ : ℂ) * _ at e
      rw [show (χ ⟨g, h₂⟩ : ℂ) = (χ ⟨g, m₁⟩ : ℂ) from rfl, e, mul_assoc, hcancel, mul_one]
  · -- `k + 1` is the critical depth of `β`: the critical twist of BK93 (3.3.18)
    have hlt := hSs.2
    rw [hSr] at hlt
    have hk0 : criticalExponent S.chain S.b = ((-((k + 1 : ℕ) : ℤ) : ℤ) : WithBot ℤ) := by
      cases hc : criticalExponent S.chain S.b with
      | bot => exact (hcrit (by rw [hc]; exact WithBot.bot_lt_coe _)).elim
      | coe j =>
        rw [hc] at hlt hcrit
        have h1 := WithBot.coe_lt_coe.mp hlt
        have h2 : ¬ j < -((k + 1 : ℕ) : ℤ) := fun h => hcrit (WithBot.coe_lt_coe.mpr h)
        congr 1
        push_cast at h1 h2 ⊢
        omega
    have happrox : (S.atDepthZero (h0.trans_lt S.r_lt_n)).IsCriticalApproximation T :=
      ⟨horder, hTn.trans rfl, hTs, by change criticalExponent S.chain S.b = _; rw [hk0, hTr],
        hbT⟩
    have hr : finiteCriticalDepth S.chain S.n S.b = ((k + 1 : ℕ) : ℤ) :=
      finiteCriticalDepth_of_criticalExponent_eq S.chain S.n _ S.b hk0
    obtain ⟨-, -, hc, -, -⟩ := hRestr F V ψF hψ (S.atDepthZero (h0.trans_lt S.r_lt_n)) rfl hS0
      (q.atDepthZero h0)
    obtain ⟨hH, e, he⟩ := hc T happrox qT k
      (by show finiteCriticalDepth S.chain S.n S.b / 2 ≤ _; rw [hr]; push_cast; omega)
      (by show _ < finiteCriticalDepth S.chain S.n S.b; rw [hr]; push_cast; omega)
    change simpleHGroup S.chain S.n S.b q.tail (k + 1) =
      simpleHGroup T.chain T.n T.b qT.tail (k + 1) at hH
    have key : ∀ (θ : simpleCharacters ψF S.chain S.n S.b q.tail k) (g : G)
        (h₁ : g ∈ simpleHGroup S.chain S.n S.b q.tail (k + 1))
        (h₂ : g ∈ simpleHGroup T.chain T.n T.b qT.tail (k + 1)),
        (θ.1 ⟨g, h₁⟩ : ℂ) = (e θ).1 ⟨g, h₂⟩ *
          elementCharacter (traceCharacter ψF) (S.b - T.b) g := by
      intro θ g h₁ h₂
      obtain ⟨m₁, m₂, hv⟩ := he θ ⟨g, h₂⟩
      change ((e θ).1 ⟨g, m₁⟩ : ℂ) = (θ.1 ⟨g, m₂⟩ : ℂ) *
        (elementCharacter (traceCharacter ψF) (S.b - T.b) g)⁻¹ at hv
      rw [show ((e θ).1 ⟨g, h₂⟩ : ℂ) = ((e θ).1 ⟨g, m₁⟩ : ℂ) from rfl, hv, mul_assoc,
        inv_mul_cancel₀ (hne g), mul_one]
    refine ⟨hH, fun θ hθ => ⟨(e ⟨θ, hθ⟩).1, (e ⟨θ, hθ⟩).2, key ⟨θ, hθ⟩⟩, fun χ hχ => ?_⟩
    refine ⟨(e.symm ⟨χ, hχ⟩).1, (e.symm ⟨χ, hχ⟩).2, fun g h₁ h₂ => ?_⟩
    have := key (e.symm ⟨χ, hχ⟩) g h₁ h₂
    rwa [Equiv.apply_symm_apply] at this

/-- **BK93 (3.3.18), (3.3.20)(ii)** for pairs: `TwistDecompositionAt` for every lattice chain
and depth, for `ψ_F` trivial on `𝔭_F` and nontrivial on `𝔬_F`. -/
theorem twistDecompositionAt (hApprox : PureStratumSimpleApproximationStatement.{uF, uV})
    (hChoice : SimpleCharacterChoiceStatement.{uF, uV})
    (hRestr : SimpleCharacterRestrictionStatement.{uF, uV}) (hψ : IsBKAdditiveCharacter ψF)
    (L : LatticeChain 𝒪[F] F V) (n : ℤ) (k : ℕ) : TwistDecompositionAt ψF L n k := by
  intro T S hb
  obtain ⟨hTL, hTn, hTr, hTs⟩ := T.2
  obtain ⟨hSL, hSn, hSr, hSs⟩ := S.2
  have hcorr := fun q qT => twist_correspondence ψF hChoice hRestr hψ k T.1 S.1
    (hTL.trans hSL.symm) (hTn.trans hSn.symm) hTr hSr hTs hSs (by rw [hSL]; exact hb) q qT
  constructor
  · intro P hP
    simp only [simpleCharacterPairs, Set.mem_iUnion, Set.mem_image] at hP
    obtain ⟨q, θ, hθ, rfl⟩ := hP
    obtain ⟨qT, -, -⟩ := Stratum.exists_exact_definingSequenceChoice hApprox T.1 hTs
    obtain ⟨hH, h₁, -⟩ := hcorr q qT
    obtain ⟨χ, hχ, hv⟩ := h₁ θ hθ
    refine ⟨⟨_, χ⟩, Set.mem_iUnion.mpr ⟨qT, χ, hχ, rfl⟩, hH.symm, fun g => ?_⟩
    have hg₁ : (g : G) ∈ simpleHGroup S.1.chain S.1.n S.1.b q.tail (k + 1) :=
      (congrArg (fun K : Subgroup G => (g : G) ∈ K) hH).mpr g.2
    exact ⟨hg₁, g.2, hv g hg₁ g.2⟩
  · intro ϑ' hϑ'
    simp only [simpleCharacterPairs, Set.mem_iUnion, Set.mem_image] at hϑ'
    obtain ⟨qT, χ, hχ, rfl⟩ := hϑ'
    obtain ⟨q, -, -⟩ := Stratum.exists_exact_definingSequenceChoice hApprox S.1 hSs
    obtain ⟨hH, -, h₂⟩ := hcorr q qT
    obtain ⟨θ, hθ, hv⟩ := h₂ χ hχ
    refine ⟨⟨_, θ⟩, Set.mem_iUnion.mpr ⟨q, θ, hθ, rfl⟩, hH, fun g => ?_⟩
    have hg₁ : (g : G) ∈ simpleHGroup S.1.chain S.1.n S.1.b q.tail (k + 1) :=
      (congrArg (fun K : Subgroup G => (g : G) ∈ K) hH).mpr g.2
    exact ⟨hg₁, g.2, hv g hg₁ g.2⟩

end Langlands.BushnellKutzko
