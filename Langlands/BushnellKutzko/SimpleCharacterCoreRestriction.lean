import Langlands.BushnellKutzko.SimpleCharacterCoreFibre
import Langlands.BushnellKutzko.SimpleCharacterIntertwiningStatement

/-! # Restricting a simple character to the depth of a core approximation -/

open ValuativeRel
open scoped Pointwise

namespace Langlands.BushnellKutzko

universe uF uV uG

private theorem characterSelfIntertwining_eq_of_agreesOn
    {G : Type uG} [Group G] {H K : Subgroup G} (h : H = K)
    {χ : H →* ℂˣ} {η : K →* ℂˣ} (ha : characterAgreesOn H χ η (fun _ => 1)) :
    characterSelfIntertwining χ = characterSelfIntertwining η := by
  cases h
  have heq : χ = η := by
    ext g
    obtain ⟨_, _, he⟩ := ha g
    simpa only [mul_one] using he
  rw [heq]

variable {F : Type uF} [Field F] [ValuativeRel F] [TopologicalSpace F]
  [IsNonarchimedeanLocalField F] {V : Type uV} [AddCommGroup V] [Module F V]

local notation "A" => Module.End F V
local notation "G" => (Module.End F V)ˣ
local notation "Hc(" S "," q "," m ")" => simpleHGroup (Stratum.chain S) (Stratum.n S) (Stratum.b S)
  (Stratum.DefiningSequenceChoice.tail q) (m + 1)
local notation "Cc(" ψ "," S "," q "," m ")" => simpleCharacters ψ (Stratum.chain S) (Stratum.n S)
  (Stratum.b S) (Stratum.DefiningSequenceChoice.tail q) m

private theorem restriction_mem_of_adjacent (hrestriction : SimpleCharacterRestrictionStatement.{uF, uV})
    (ψF : AddChar F ℂ) (hψ : IsBKAdditiveCharacter ψF)
    {S : Stratum 𝒪[F] F V} (q : S.DefiningSequenceChoice) (hS : S.IsSimple) (hr : 0 ≤ S.r)
    {m k : ℕ} (hmk : m ≤ k) (hkn : (k : ℤ) < S.n) {θ : Hc(S, q, m) →* ℂˣ}
    (hθ : θ ∈ Cc(ψF, S, q, m)) :
    simpleCharacterRestriction S q hmk θ ∈ Cc(ψF, S, q, k) := by
  let S₀ := S.atDepthZero (hr.trans_lt S.r_lt_n)
  let q₀ := q.atDepthZero hr
  have hres (j : ℕ) (hj : (j : ℤ) + 1 < S.n) :
      (simpleCharacterRestriction S q (Nat.le_succ j)) '' (Cc(ψF, S, q, j)) = Cc(ψF, S, q, (j + 1)) :=
    (hrestriction F V ψF hψ S₀ rfl (Stratum.isSimple_atDepthZero hS hr) q₀).2.2.2.1 j hj
  induction k, hmk using Nat.le_induction with
  | base =>
    have heq : simpleCharacterRestriction S q (le_refl m) θ = θ := by
      ext g
      rfl
    rwa [heq]
  | succ j hmj ih =>
    have hθj := ih (by omega : (j : ℤ) < S.n)
    have heq : simpleCharacterRestriction S q (Nat.le_succ_of_le hmj) θ =
        simpleCharacterRestriction S q (Nat.le_succ j) (simpleCharacterRestriction S q hmj θ) := by
      ext g
      rfl
    rw [heq, ← hres j (by omega)]
    exact ⟨_, hθj, rfl⟩

/-- When the restriction index is at least the core approximation depth, the
core twist becomes trivial and the restricted character belongs to the core set. -/
theorem SimpleCharacterCore.restriction_agrees_on_core
    (hgroups : SimpleStratumGroupPropertiesStatement.{uF, uV})
    (hrestriction : SimpleCharacterRestrictionStatement.{uF, uV})
    {ψF : AddChar F ℂ} (hψ : IsBKAdditiveCharacter ψF)
    {S : Stratum 𝒪[F] F V} {q : S.DefiningSequenceChoice} {m k : ℕ}
    (hS : S.IsSimple) (hr : 0 ≤ S.r) (core : SimpleCharacterCore ψF S q m)
    (hmk : m ≤ k) (hdepth : core.stratum.r ≤ (k : ℤ)) (hkn : (k : ℤ) < S.n)
    {θ : Hc(S, q, m) →* ℂˣ} (hθ : θ ∈ Cc(ψF, S, q, m)) :
    ∃ θ₀ ∈ Cc(ψF, core.stratum, core.sequence, k),
      characterAgreesOn (Hc(S, q, k)) (simpleCharacterRestriction S q hmk θ) θ₀ (fun _ => 1) := by
  obtain ⟨χ, hχ, hag⟩ := core.twist.1 θ hθ
  have hd := core.domain_eq_of_le hgroups hS hr hmk
  have hk' : (k : ℤ) < core.stratum.n := by rwa [core.level_eq]
  refine ⟨simpleCharacterRestriction core.stratum core.sequence hmk χ,
    restriction_mem_of_adjacent hrestriction ψF hψ core.sequence core.isSimple
      (hr.trans core.depth_le) hmk hk' hχ, ?_⟩
  intro g
  let g₀ : Hc(S, q, m) := Subgroup.inclusion
    (simpleHGroup_antitone S.chain S.n S.b q.tail (Nat.succ_le_succ hmk)) g
  obtain ⟨_, _, he⟩ := hag g₀
  let hk : (g : G) ∈ Hc(core.stratum, core.sequence, k) := hd ▸ g.property
  refine ⟨g.property, hk, ?_⟩
  have hb : S.b - core.stratum.b ∈ S.chain.endFiltration (-(k : ℤ)) :=
    S.chain.endFiltration_antitone (neg_le_neg hdepth) core.congruence
  have hdual := (additiveDuality F V S.chain ψF hψ.1 hψ.2).1 ((k : ℤ) + 1)
  have hb' : S.b - core.stratum.b ∈ additiveDual (traceCharacter ψF)
      (S.chain.endFiltration ((k : ℤ) + 1) : Set A) := by
    rw [hdual, show (1 : ℤ) - (k + 1) = -k by omega]
    exact hb
  have hg := simpleHGroup_le_unitFiltration S.chain S.n S.b q.tail (k + 1) g.property
  have htriv : elementCharacter (traceCharacter ψF) (S.b - core.stratum.b) g = 1 :=
    hb' (((g : G) : A) - 1) hg.2.2
  have he' : (simpleCharacterRestriction S q hmk θ g : ℂ) =
      (simpleCharacterRestriction core.stratum core.sequence hmk χ ⟨g, hk⟩ : ℂ) *
        elementCharacter (traceCharacter ψF) (S.b - core.stratum.b) g := he
  simpa only [htriv] using he'

omit [TopologicalSpace F] [IsNonarchimedeanLocalField F] in
private theorem one_mem_simpleCharacterIntertwiningFactor (S : Stratum 𝒪[F] F V)
    (q : S.DefiningSequenceChoice) (k : ℕ) : 1 ∈ simpleCharacterIntertwiningFactor S q k := by
  classical
  unfold simpleCharacterIntertwiningFactor
  split <;> simp

/-- If a restriction is far enough to be a core character and remains below the
core critical depth, its self-intertwining contains the core centralizer. -/
theorem SimpleCharacterCore.centralizer_subset_intertwining_restriction
    (hgroups : SimpleStratumGroupPropertiesStatement.{uF, uV})
    (hrestriction : SimpleCharacterRestrictionStatement.{uF, uV})
    (hintertwining : SimpleCharacterIntertwiningStatement.{uF, uV})
    {ψF : AddChar F ℂ} (hψ : IsBKAdditiveCharacter ψF)
    {S : Stratum 𝒪[F] F V} {q : S.DefiningSequenceChoice} {m k : ℕ}
    (hS : S.IsSimple) (hr : 0 ≤ S.r) (core : SimpleCharacterCore ψF S q m)
    (hmk : m ≤ k) (hdepth : core.stratum.r ≤ (k : ℤ)) (hkn : (k : ℤ) < S.n)
    (hcrit : ((k : ℤ) : WithTop ℤ) < simpleCriticalDepth core.stratum.chain core.stratum.b)
    {θ : Hc(S, q, m) →* ℂˣ} (hθ : θ ∈ Cc(ψF, S, q, m)) :
    (centralizerUnitGroup core.stratum.b : Set G) ⊆
      characterSelfIntertwining (simpleCharacterRestriction S q hmk θ) := by
  obtain ⟨χ, hχ, ha⟩ := core.restriction_agrees_on_core hgroups hrestriction hψ hS hr hmk hdepth hkn hθ
  rw [characterSelfIntertwining_eq_of_agreesOn (core.domain_eq_of_le hgroups hS hr hmk) ha]
  let T := core.stratum
  let hrT := hr.trans core.depth_le
  let T₀ := T.atDepthZero (hrT.trans_lt T.r_lt_n)
  let q₀ := core.sequence.atDepthZero hrT
  have hk : (k : ℤ) < T.n := by rwa [core.level_eq]
  obtain ⟨hI, _⟩ := hintertwining F V ψF hψ T₀ rfl (Stratum.isSimple_atDepthZero core.isSimple hrT)
    q₀ k hk hcrit χ hχ
  intro g hg
  have h₁ := one_mem_simpleCharacterIntertwiningFactor T₀ q₀ k
  have hg' : g ∈ (centralizerUnitGroup T₀.b : Set G) := hg
  have hmem : g ∈ simpleCharacterIntertwiningFactor T₀ q₀ k * (centralizerUnitGroup T₀.b : Set G) *
      simpleCharacterIntertwiningFactor T₀ q₀ k := by
    simpa only [one_mul, mul_one] using Set.mul_mem_mul (Set.mul_mem_mul h₁ hg') h₁
  exact hI.symm ▸ hmem

/-- For two characters in the same simple character set at a depth at least that
of the core, their ratio is intertwined by the self-intertwining of either character. -/
theorem SimpleCharacterCore.selfIntertwining_subset_ratio_of_depth_le
    (hgroups : SimpleStratumGroupPropertiesStatement.{uF, uV})
    (hrestriction : SimpleCharacterRestrictionStatement.{uF, uV})
    (hintertwining : SimpleCharacterIntertwiningStatement.{uF, uV})
    {ψF : AddChar F ℂ} (hψ : IsBKAdditiveCharacter ψF)
    {S : Stratum 𝒪[F] F V} {q : S.DefiningSequenceChoice} {m : ℕ}
    (hS : S.IsSimple) (hr : 0 ≤ S.r) (core : SimpleCharacterCore ψF S q m)
    (hdepth : core.stratum.r ≤ (m : ℤ)) (hmn : (m : ℤ) < S.n)
    (hcrit : ((m : ℤ) : WithTop ℤ) < simpleCriticalDepth core.stratum.chain core.stratum.b)
    {χ θ : Hc(S, q, m) →* ℂˣ} (hχ : χ ∈ Cc(ψF, S, q, m))
    (hθ : θ ∈ Cc(ψF, S, q, m)) :
    characterSelfIntertwining θ ⊆ characterSelfIntertwining (χ / θ) := by
  have hI (η : Hc(S, q, m) →* ℂˣ) (hη : η ∈ Cc(ψF, S, q, m)) :
      characterSelfIntertwining η =
        simpleCharacterIntertwiningFactor core.stratum core.sequence m *
          (centralizerUnitGroup core.stratum.b : Set G) *
          simpleCharacterIntertwiningFactor core.stratum core.sequence m := by
    obtain ⟨η₀, hη₀, hag⟩ := core.restriction_agrees_on_core hgroups hrestriction hψ hS hr
      (le_refl m) hdepth hmn hη
    have heq : simpleCharacterRestriction S q (le_refl m) η = η := by
      ext g
      rfl
    rw [heq] at hag
    refine (characterSelfIntertwining_eq_of_agreesOn core.domain_eq hag).trans ?_
    have hrT := hr.trans core.depth_le
    have hmT : (m : ℤ) < core.stratum.n := core.level_eq.symm ▸ hmn
    exact (hintertwining F V ψF hψ (core.stratum.atDepthZero (hrT.trans_lt core.stratum.r_lt_n))
      rfl (Stratum.isSimple_atDepthZero core.isSimple hrT) (core.sequence.atDepthZero hrT)
      m hmT hcrit η₀ hη₀).1
  intro a ha g hg
  have haχ : a ∈ characterSelfIntertwining χ := ((hI θ hθ).trans (hI χ hχ).symm) ▸ ha
  rw [MonoidHom.div_apply, MonoidHom.div_apply, haχ g hg, ha g hg]

/-- The core centralizer lies in the self-intertwining of a common restriction
as soon as its depth reaches the core and is still in its simple range. -/
def SimpleCharacterCoreRestrictionStatement : Prop :=
  SimpleStratumGroupPropertiesStatement.{uF, uV} →
  SimpleCharacterRestrictionStatement.{uF, uV} →
  SimpleCharacterIntertwiningStatement.{uF, uV} →
  ∀ (F : Type uF) [Field F] [ValuativeRel F] [TopologicalSpace F]
    [IsNonarchimedeanLocalField F] (V : Type uV) [AddCommGroup V] [Module F V]
    (ψF : AddChar F ℂ), IsBKAdditiveCharacter ψF →
    ∀ (S : Stratum 𝒪[F] F V) (q : S.DefiningSequenceChoice), S.IsSimple → 0 ≤ S.r →
      ∀ (m k : ℕ) (core : SimpleCharacterCore ψF S q m) (hmk : m ≤ k),
        core.stratum.r ≤ (k : ℤ) → (k : ℤ) < S.n →
        ((k : ℤ) : WithTop ℤ) < simpleCriticalDepth core.stratum.chain core.stratum.b →
        ∀ θ ∈ Cc(ψF, S, q, m), (centralizerUnitGroup core.stratum.b : Set (Module.End F V)ˣ) ⊆
          characterSelfIntertwining (simpleCharacterRestriction S q hmk θ)

theorem simpleCharacterCoreRestriction : SimpleCharacterCoreRestrictionStatement.{uF, uV} := by
  intro hgroups hrestriction hintertwining F _ _ _ _ V _ _ ψF hψ S q hS hr m k core hmk hd hn hc θ hθ
  exact core.centralizer_subset_intertwining_restriction hgroups hrestriction hintertwining hψ hS
    hr hmk hd hn hc hθ

end Langlands.BushnellKutzko
