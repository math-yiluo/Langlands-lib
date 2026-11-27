import Langlands.BushnellKutzko.ClassCoverFibre
import Langlands.BushnellKutzko.SimpleIntertwiningProof
import Langlands.BushnellKutzko.SimpleCharacterCovarianceStatement

/-! # Covering simple-character classes: conjugacy of twisted characters (BK94 (2.8)) -/

open ValuativeRel
open scoped Pointwise

noncomputable section

namespace Langlands.BushnellKutzko

universe uF uV

variable {F : Type uF} [Field F] [ValuativeRel F] [TopologicalSpace F]
  [IsNonarchimedeanLocalField F] {V : Type uV} [AddCommGroup V] [Module F V]

local notation "A" => Module.End F V
local notation "G" => (Module.End F V)ˣ

omit [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F] in
/-- A scalar element commutes with every unit. -/
theorem mem_centralizerUnits_of_elementAlgebra_eq_bot {γ : A} (h : elementAlgebra γ = ⊥)
    (x : G) : x ∈ centralizerUnits γ := by
  have hγ : γ ∈ elementAlgebra γ := Algebra.subset_adjoin rfl
  rw [h, Algebra.mem_bot] at hγ
  obtain ⟨c, rfl⟩ := hγ
  exact Algebra.commutes c (x : A)

omit [TopologicalSpace F] [IsNonarchimedeanLocalField F] in
/-- The intertwining neighbourhood of BK93 (1.5.8) for `[𝔄,n,t,γ]` lies in the factor `Y` of
BK93 (3.3.2) at index `t`. -/
theorem simpleIntertwiningNeighborhood_subset (S T : Stratum 𝒪[F] F V)
    (q : S.DefiningSequenceChoice) (t : ℕ) (hchain : T.chain = S.chain) (hb : T.b = S.b)
    (ht : T.r = t) (hne : elementAlgebra S.b ≠ ⊥) :
    T.simpleIntertwiningNeighborhood ⊆ simpleCharacterIntertwiningFactor S q t := by
  intro g hg
  unfold simpleCharacterIntertwiningFactor
  rw [ite_eq_right hne]
  show (g : A) - 1 ∈ centralizerLattice S.chain S.b (finiteCriticalDepth S.chain S.n S.b - (t : ℤ)) *
      adjointLattice S.chain S.b (-finiteCriticalDepth S.chain S.n S.b) ⊔
    simpleJLayer S.chain S.n S.b q.tail (simpleJCutoff (finiteCriticalDepth S.chain S.n S.b)).toNat
  rcases hg with ⟨-, rfl⟩ | ⟨k', hk', hg⟩
  · simp
  · rw [hchain, hb] at hk' hg
    have hr : finiteCriticalDepth S.chain S.n S.b = -k' :=
      finiteCriticalDepth_of_criticalExponent_eq S.chain S.n (-k') S.b (by rw [neg_neg]; exact hk')
    rw [hr, neg_neg]
    refine Submodule.mem_sup_left ?_
    rw [ht, show -((t : ℤ) + k') = -k' - t by ring] at hg
    exact hg

/-- **BK94 (2.8), (ii) ⇒ (iii),** for the twist coefficients `β_i - γ`, from BK93 (1.5.8) and
(3.3.9). -/
theorem twistConjugacyAt [FiniteDimensional F V] (ψF : AddChar F ℂ)
    (hApprox : PureStratumSimpleApproximationStatement.{uF, uV})
    (hConj : SimpleCharacterConjugationStatement.{uF, uV})
    (hChoice : SimpleCharacterChoiceStatement.{uF, uV})
    (hCov : SimpleCharacterCovarianceStatement.{uF, uV}) (hψ : IsBKAdditiveCharacter ψF)
    (L : LatticeChain 𝒪[F] F V) (n : ℤ) (k : ℕ) (hk : (k : ℤ) + 1 < n) :
    TwistConjugacyAt ψF L n k := by
  intro T ϑ hϑ S₁ S₂ P₁ P₂ hb₁ hb₂ hP₁ hP₂ h₁ h₂ ha₁ ha₂ hS
  obtain ⟨x, hx, hxS⟩ := hS
  obtain ⟨hTL, hTn, hTr, hTs⟩ := T.2
  have hP₁x : P₁.conj x ∈ simpleCharacterPairs ψF S₂.1 k :=
    simpleCharacterPairs_conj_mem ψF hApprox hConj hChoice hψ L n k S₁ S₂ x hx hxS P₁ hP₁
  have hdom : (P₁.conj x).1 = P₂.1 := by
    obtain ⟨q₂, -, -⟩ := Stratum.exists_exact_definingSequenceChoice hApprox S₂.1 S₂.2.2.2.2
    rw [simpleCharacterPairs_eq_choiceImage ψF hChoice hψ S₂.1 k S₂.2.2.2.1 S₂.2.2.2.2 q₂] at hP₁x hP₂
    obtain ⟨_, -, e₁⟩ := hP₁x
    obtain ⟨_, -, e₂⟩ := hP₂
    rw [← e₁, ← e₂]
  simp only [simpleCharacterPairs, Set.mem_iUnion, Set.mem_image] at hϑ
  obtain ⟨q, ϑ₀, hϑ₀, rfl⟩ := hϑ
  have h0 : (0 : ℤ) ≤ T.1.r := by rw [hTr]; positivity
  have hdepth := hTs.r_lt_simpleCriticalDepth
  rw [hTr] at hdepth
  have hdepth' : ((k : ℤ) : WithTop ℤ) < simpleCriticalDepth T.1.chain T.1.b :=
    lt_of_le_of_lt (WithTop.coe_le_coe.mpr (by push_cast; omega)) hdepth
  have hcov := hCov F V ψF hψ (T.1.atDepthZero (h0.trans_lt T.1.r_lt_n)) rfl
    (Stratum.isSimple_atDepthZero hTs h0) (q.atDepthZero h0) k (k + 1)
    (by change (k : ℤ) < T.1.n; omega) (by change ((k + 1 : ℕ) : ℤ) < T.1.n; push_cast; omega)
    hdepth' hdepth (by omega) ϑ₀ hϑ₀
  have hxY : x ∈ simpleCharacterIntertwiningFactor (T.1.atDepthZero (h0.trans_lt T.1.r_lt_n))
        (q.atDepthZero h0) (k + 1) * (centralizerUnitGroup T.1.b : Set G) *
      simpleCharacterIntertwiningFactor (T.1.atDepthZero (h0.trans_lt T.1.r_lt_n))
        (q.atDepthZero h0) (k + 1) := by
    by_cases hne : elementAlgebra T.1.b = ⊥
    · have hY : simpleCharacterIntertwiningFactor (T.1.atDepthZero (h0.trans_lt T.1.r_lt_n))
          (q.atDepthZero h0) (k + 1) = {1} := by
        unfold simpleCharacterIntertwiningFactor
        exact ite_eq_left hne
      rw [hY]
      exact ⟨1 * x, ⟨1, rfl, x, mem_centralizerUnits_of_elementAlgebra_eq_bot hne x, rfl⟩, 1, rfl,
        by simp⟩
    · have hint : x ∈ T.1.formalSelfIntertwining := by
        refine ⟨S₁.1.b, ?_, ?_⟩
        · change S₁.1.b - T.1.b ∈ T.1.chain.endFiltration (-T.1.r)
          rw [hTL, hTr]
          exact hb₁
        · change (↑x⁻¹ : A) * S₁.1.b * (x : A) - T.1.b ∈ T.1.chain.endFiltration (-T.1.r)
          rw [hTL, hTr]
          have hδ : (↑x⁻¹ : A) * S₁.1.b * (x : A) - S₂.1.b ∈
              L.endFiltration (-((k + 1 : ℕ) : ℤ)) := by
            have := neg_mem hxS
            rw [neg_sub] at this
            exact L.endFiltration_antitone (by push_cast; omega) this
          have := add_mem hδ hb₂
          rwa [sub_add_sub_cancel] at this
      rw [simpleIntertwining F V T.1 hTs] at hint
      have hN := simpleIntertwiningNeighborhood_subset (T.1.atDepthZero (h0.trans_lt T.1.r_lt_n))
        T.1 (q.atDepthZero h0) (k + 1) rfl rfl hTr hne
      exact Set.mul_subset_mul (Set.mul_subset_mul hN (fun y hy => hy)) hN hint
  refine ⟨⟨x, hx⟩, CharacterPair.ext_of_eq hdom (fun g hg₁ hg₂ => ?_)⟩
  have hxg : x * g * x⁻¹ ∈ P₁.1 := CharacterPair.mem_conj_fst.mp hg₁
  rw [CharacterPair.conj_snd_apply x P₁ g hg₁ hxg]
  apply Units.ext
  have hgH : g ∈ simpleHGroup T.1.chain T.1.n T.1.b q.tail (k + 1) :=
    (congrArg (fun K : Subgroup G => g ∈ K) h₂).mp hg₂
  have hxgH : x * g * x⁻¹ ∈ simpleHGroup T.1.chain T.1.n T.1.b q.tail (k + 1) :=
    (congrArg (fun K : Subgroup G => x * g * x⁻¹ ∈ K) h₁).mp hxg
  obtain ⟨m₁, m₁', e₁⟩ := ha₁ ⟨x * g * x⁻¹, hxgH⟩
  obtain ⟨m₂, m₂', e₂⟩ := ha₂ ⟨g, hgH⟩
  have e₁' : (P₁.2 ⟨x * g * x⁻¹, hxg⟩ : ℂ) = (ϑ₀ ⟨x * g * x⁻¹, hxgH⟩ : ℂ) *
      elementCharacter (traceCharacter ψF) (S₁.1.b - T.1.b) (x * g * x⁻¹) := e₁
  have e₂' : (P₂.2 ⟨g, hg₂⟩ : ℂ) = (ϑ₀ ⟨g, hgH⟩ : ℂ) *
      elementCharacter (traceCharacter ψF) (S₂.1.b - T.1.b) g := e₂
  have e₃' : (ϑ₀ ⟨x * g * x⁻¹, hxgH⟩ : ℂ) = (ϑ₀ ⟨g, hgH⟩ : ℂ) *
      elementCharacter (traceCharacter ψF) ((↑x⁻¹ : A) * T.1.b * (x : A) - T.1.b) g :=
    hcov x hxY ⟨g, hgH⟩ hxgH
  rw [e₁', e₂', e₃', elementCharacter_conj, mul_assoc, ← elementCharacter_add]
  congr 1
  have hgU : g ∈ L.unitFiltration (k + 1) := by
    have := simpleHGroup_le_unitFiltration T.1.chain T.1.n T.1.b q.tail (k + 1) hgH
    rwa [hTL] at this
  have htriv := elementCharacter_eq_one_of_depth L ψF hψ (neg_mem hxS) (k := k + 1)
    (by push_cast; omega) hgU
  rw [← mul_one (elementCharacter (traceCharacter ψF) (S₂.1.b - T.1.b) g), ← htriv,
    ← elementCharacter_add]
  congr 1
  simp only [mul_sub, sub_mul]
  abel

end Langlands.BushnellKutzko
