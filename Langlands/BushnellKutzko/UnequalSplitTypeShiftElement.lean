import Langlands.BushnellKutzko.ShiftedSimpleHGroup
import Langlands.BushnellKutzko.UnequalSplitTypeAdjust
import Langlands.BushnellKutzko.UnequalSplitTypeRefinement

/-! # The shift element for a split type of level `(x, y)` (BK93 (8.2.9), (8.2.16))

For block idempotents `e₁, e₂` of `𝔅`, the element `z = ζ + e₂` of (8.2.9) commutes with `β`
and may change the twisting element `c`. A unit `g₀ = 1 + u` with `u ∈ e₁ (𝔔^{r−m} 𝔑_{−r}) e₁`
accounts for this change. The unit `y = g₀ z` moves `M_{j-1}` into `M_j`, conjugates `H^m` like `z`, and preserves
`θ ψ_c` on `H^m ∩ z⁻¹ H^m z`. -/

noncomputable section

open ValuativeRel

namespace Langlands.BushnellKutzko.SplitBlocks

universe uF uV

variable {F : Type uF} [Field F] [ValuativeRel F] [TopologicalSpace F]
  [IsNonarchimedeanLocalField F] {V : Type uV} [AddCommGroup V] [Module F V]

local notation "A" => Module.End F V
local notation "G" => (Module.End F V)ˣ

omit [TopologicalSpace F] [IsNonarchimedeanLocalField F] in
/-- Products `𝔔^k 𝔑_l` are stable under multiplication by elements of `𝔅` on either side. -/
theorem mul_mul_mem_centralizer_mul_adjoint (L : LatticeChain 𝒪[F] F V) (β : A) {k l : ℤ}
    {e e' x : A} (he : e ∈ centralizerLattice L β 0) (he' : e' ∈ centralizerLattice L β 0)
    (hx : x ∈ centralizerLattice L β k * adjointLattice L β l) :
    e * x * e' ∈ centralizerLattice L β k * adjointLattice L β l := by
  have hadj : ∀ a b : A, adjointMap 𝒪[F] a b = a * b - b * a := fun _ _ => rfl
  have hcomm : ∀ a : A, a ∈ centralizerLattice L β 0 → β * a = a * β := fun a ha => by
    have h : adjointMap 𝒪[F] β a = 0 := LinearMap.mem_ker.mp ha.2
    rw [hadj] at h
    exact sub_eq_zero.mp h
  refine Submodule.mul_induction_on (C := fun x => e * x * e' ∈
    centralizerLattice L β k * adjointLattice L β l) hx ?_ ?_
  · intro p hp n hn
    rw [show e * (p * n) * e' = (e * p) * (n * e') by noncomm_ring]
    refine Submodule.mul_mem_mul ⟨?_, ?_⟩ ⟨?_, ?_⟩
    · simpa using L.mul_mem_endFiltration he.1 hp.1
    · change e * p ∈ (adjointMap 𝒪[F] β).ker
      rw [LinearMap.mem_ker, hadj]
      have h1 := hcomm e he
      have h2 : adjointMap 𝒪[F] β p = 0 := LinearMap.mem_ker.mp hp.2
      rw [hadj, sub_eq_zero] at h2
      rw [← mul_assoc, h1, mul_assoc, h2, mul_assoc, sub_self]
    · simpa using L.mul_mem_endFiltration hn.1 he'.1
    · have h2 : β * n - n * β ∈ L.endFiltration l := by
        have := hn.2
        rw [SetLike.mem_coe, Submodule.mem_comap, hadj] at this
        exact this
      change n * e' ∈ Submodule.comap (adjointMap 𝒪[F] β) (L.endFiltration l)
      rw [Submodule.mem_comap, hadj]
      have h1 := hcomm e' he'
      have : β * (n * e') - n * e' * β = (β * n - n * β) * e' := by
        rw [sub_mul, mul_assoc, ← h1, mul_assoc]
        noncomm_ring
      rw [this]
      simpa using L.mul_mem_endFiltration h2 he'.1
  · intro a b ha hb
    rw [mul_add, add_mul]
    exact add_mem ha hb

/-- **The corrected shift element (BK93 (8.2.9), (8.2.16)).** Let `[𝔄, n, 0, β]` be simple,
with `θ ∈ C(𝔄, m−1, β)` on `H = H^m` with `m = i + 1`, and `ϑ = θ ψ_c` with
`c ∈ 𝔓^{−m}` split by complementary idempotents `e₁, e₂` of `𝔅`. Let `ζ ∈ 𝔓`, `ζ' ∈ 𝔓^{−1}`
be mutually inverse on the first block, commuting with `β`, such that a tame corestriction
kills `ζ c₁₁ ζ' − c₁₁` for `c₁₁ = e₁ c e₁`. Then `z = ζ + e₂` is a unit, and a corrected shift `y` satisfies `y M_{j−1} y⁻¹ ⊆ M_j`, conjugates into `H` exactly when `z` does,
satisfies `ϑ(y κ y⁻¹) = θ(z κ z⁻¹) ψ_c(κ)`, and preserves `ϑ` on `H ∩ z⁻¹ H z`. -/
abbrev SplitTypeShiftStatement : Prop :=
  ∀ {E : Type*} [Field E] [Algebra F E] [Module E V]
    [IsScalarTower F E V] (S : Stratum 𝒪[F] F V) (_h0 : S.r = 0) (_hs : S.IsSimple)
    (q : S.DefiningSequenceChoice) (i : ℕ) (_hin : (i : ℤ) + 1 < S.n)
    (_hcrit : (((i + 1 : ℕ) : ℤ) : WithTop ℤ) < simpleCriticalDepth S.chain S.b)
    {ψF : AddChar F ℂ} (_hψ : IsBKAdditiveCharacter ψF)
    {θ : simpleHGroup S.chain S.n S.b q.tail (i + 1) →* ℂˣ}
    (_hθ : θ ∈ simpleCharacters ψF S.chain S.n S.b q.tail i)
    {βE : E} (_hβES : subfieldEmbedding F E V βE = S.b) (_hβE : Algebra.adjoin F ({βE} : Set E) = ⊤)
    (s : TameCorestriction 𝒪[F] F E V) {c : A}
    (_hc : c ∈ S.chain.endFiltration (-((i + 1 : ℕ) : ℤ)))
    {e₁ e₂ ζ ζ' : A} (_hadd : e₁ + e₂ = 1) (_hmul : e₁ * e₂ = 0) (h₂₁ : e₂ * e₁ = 0)
    (_he₁B : e₁ ∈ centralizerLattice S.chain S.b 0) (_he₂0 : e₂ ∈ S.chain.endFiltration 0)
    (_hζ : ζ ∈ S.chain.endFiltration 1) (_hζ' : ζ' ∈ S.chain.endFiltration (-1))
    (_hζζ' : ζ * ζ' = e₁) (_hζ'ζ : ζ' * ζ = e₁) (_he₁ζ : e₁ * ζ = ζ) (_hζe₁ : ζ * e₁ = ζ)
    (_he₁ζ' : e₁ * ζ' = ζ') (_hζ'e₁ : ζ' * e₁ = ζ')
    (_hζb : ζ * S.b = S.b * ζ) (_he₂b : e₂ * S.b = S.b * e₂)
    (_hc12 : e₁ * c * e₂ = 0) (_hc21 : e₂ * c * e₁ = 0)
    (_hsa : s (ζ * (e₁ * c * e₁) * ζ' - e₁ * c * e₁) = 0)
    (ϑ : simpleHGroup S.chain S.n S.b q.tail (i + 1) →* ℂˣ)
    (_hϑ : ∀ h, (ϑ h : ℂ) = (θ h : ℂ) * elementCharacter (traceCharacter ψF) c (h : G)),
    ∃ z y : G, (z : A) = ζ + e₂ ∧ ((z⁻¹ : G) : A) = ζ' + e₂ ∧
      (∀ j, ∀ u ∈ blockFiltrationUnipotent S.chain h₂₁ (j - 1),
        y * u * y⁻¹ ∈ blockFiltrationUnipotent S.chain h₂₁ j) ∧
      (∀ κ : G, y * κ * y⁻¹ ∈ simpleHGroup S.chain S.n S.b q.tail (i + 1) ↔
        z * κ * z⁻¹ ∈ simpleHGroup S.chain S.n S.b q.tail (i + 1)) ∧
      (∀ (κ : G) (hy : y * κ * y⁻¹ ∈ simpleHGroup S.chain S.n S.b q.tail (i + 1))
        (hz : z * κ * z⁻¹ ∈ simpleHGroup S.chain S.n S.b q.tail (i + 1)),
        (ϑ ⟨_, hy⟩ : ℂ) = (θ ⟨_, hz⟩ : ℂ) * elementCharacter (traceCharacter ψF) c κ) ∧
      (∀ (κ : simpleHGroup S.chain S.n S.b q.tail (i + 1))
        (hy : y * (κ : G) * y⁻¹ ∈ simpleHGroup S.chain S.n S.b q.tail (i + 1)),
        ϑ ⟨_, hy⟩ = ϑ κ)

theorem exists_shift_element : SplitTypeShiftStatement (F := F) (V := V) := by
  intro E _ _ _ _ S h0 hs q i hin hcrit ψF hψ θ hθ βE hβES hβE s c hc
    e₁ e₂ ζ ζ' hadd hmul h₂₁ he₁B _he₂0 hζ hζ' hζζ' hζ'ζ he₁ζ hζe₁ he₁ζ' hζ'e₁
    hζb he₂b hc12 hc21 hsa ϑ hϑ
  have he₁0 : e₁ ∈ S.chain.endFiltration 0 := he₁B.1
  have he₁b : e₁ * S.b = S.b * e₁ := by
    have h : adjointMap 𝒪[F] S.b e₁ = 0 := LinearMap.mem_ker.mp he₁B.2
    exact (sub_eq_zero.mp h).symm
  have he₁e₁ : e₁ * e₁ = e₁ := by
    calc e₁ * e₁ = e₁ * (e₁ + e₂) := by rw [mul_add, hmul, add_zero]
      _ = e₁ := by rw [hadd, mul_one]
  have he₂e₂ : e₂ * e₂ = e₂ := by
    calc e₂ * e₂ = (e₁ + e₂) * e₂ := by rw [add_mul, hmul, zero_add]
      _ = e₂ := by rw [hadd, one_mul]
  have hζe₂ : ζ * e₂ = 0 := by rw [← hζe₁, mul_assoc, hmul, mul_zero]
  have he₂ζ : e₂ * ζ = 0 := by rw [← he₁ζ, ← mul_assoc, h₂₁, zero_mul]
  have hζ'e₂ : ζ' * e₂ = 0 := by rw [← hζ'e₁, mul_assoc, hmul, mul_zero]
  have he₂ζ' : e₂ * ζ' = 0 := by rw [← he₁ζ', ← mul_assoc, h₂₁, zero_mul]
  -- the unit `z = ζ + e₂`
  let z : G :=
    { val := ζ + e₂
      inv := ζ' + e₂
      val_inv := by
        calc (ζ + e₂) * (ζ' + e₂) = ζ * ζ' + ζ * e₂ + e₂ * ζ' + e₂ * e₂ := by noncomm_ring
          _ = 1 := by rw [hζζ', hζe₂, he₂ζ', he₂e₂, add_zero, add_zero, hadd]
      inv_val := by
        calc (ζ' + e₂) * (ζ + e₂) = ζ' * ζ + ζ' * e₂ + e₂ * ζ + e₂ * e₂ := by noncomm_ring
          _ = 1 := by rw [hζ'ζ, hζ'e₂, he₂ζ, he₂e₂, add_zero, add_zero, hadd] }
  have hzval : (z : A) = ζ + e₂ := rfl
  have hzinv : ((z⁻¹ : G) : A) = ζ' + e₂ := rfl
  have hzb : (z : A) * S.b = S.b * (z : A) := by rw [hzval, add_mul, mul_add, hζb, he₂b]
  -- the correction `a` and the new twisting element `c' = c + a`
  set c₁₁ := e₁ * c * e₁ with hc₁₁
  set a := ζ * c₁₁ * ζ' - c₁₁ with ha
  have hc₁₁P : c₁₁ ∈ S.chain.endFiltration (-((i + 1 : ℕ) : ℤ)) :=
    mul_mul_mem_endFiltration S.chain he₁0 hc he₁0 (by ring)
  have haP : a ∈ S.chain.endFiltration (-((i + 1 : ℕ) : ℤ)) :=
    sub_mem (mul_mul_mem_endFiltration S.chain hζ hc₁₁P hζ' (by ring)) hc₁₁P
  have hea : e₁ * a * e₁ = a := by
    rw [ha, hc₁₁]
    calc e₁ * (ζ * (e₁ * c * e₁) * ζ' - e₁ * c * e₁) * e₁ =
        (e₁ * ζ) * (e₁ * c * e₁) * (ζ' * e₁) - (e₁ * e₁) * c * (e₁ * e₁) := by noncomm_ring
      _ = _ := by rw [he₁ζ, hζ'e₁, he₁e₁]
  set c' := c + a with hc'
  have hc'P : c' ∈ S.chain.endFiltration (-((i + 1 : ℕ) : ℤ)) := add_mem hc haP
  have hsc : s (c - c') = 0 := by
    have : c - c' = -a := by rw [hc']; abel
    rw [this]
    change s.toAddMonoidHom (-a) = 0
    rw [map_neg]
    exact neg_eq_zero.mpr hsa
  -- The correction is supported on the first block.
  have hcorrection : ∃ u : A, e₁ * u * e₁ = u ∧ u ∈ S.chain.endFiltration 0 ∧
      ∃ g₀ : G, (g₀ : A) = 1 + u ∧
        g₀ ∈ Subgroup.normalizer (simpleHGroup S.chain S.n S.b q.tail (i + 1) : Set G) ∧
        ∀ (h : simpleHGroup S.chain S.n S.b q.tail (i + 1))
          (hgh : g₀ * (h : G) * g₀⁻¹ ∈ simpleHGroup S.chain S.n S.b q.tail (i + 1)),
          (θ ⟨_, hgh⟩ : ℂ) * elementCharacter (traceCharacter ψF) c (g₀ * (h : G) * g₀⁻¹) =
            (θ h : ℂ) * elementCharacter (traceCharacter ψF) c' (h : G) := by
    by_cases hb : elementAlgebra S.b = ⊥
    · have hcc := sub_eq_zero.mp
        (tameCorestriction_injective_of_elementAlgebra_eq_bot S hs hβES hβE hb s
          (hsc.trans (s.toAddMonoidHom.map_zero).symm))
      refine ⟨0, by simp, zero_mem _, 1, by simp, (Subgroup.normalizer _).one_mem, fun h hh => ?_⟩
      have hconj : (1 : G) * (h : G) * 1⁻¹ = h := by simp
      rw [character_congr θ hconj hh h.2, hconj, hcc]
    · obtain ⟨x₀, hx₀, hx₀z⟩ := exists_mem_centralizer_mul_adjoint_of_corestriction_eq_zero S hs hβES
        hβE hb s (sub_mem hc hc'P) hsc
      set u := -(e₁ * x₀ * e₁) with hu
      have huQN := neg_mem (mul_mul_mem_centralizer_mul_adjoint S.chain S.b he₁B he₁B hx₀)
      have hbu : S.b * u - u * S.b = -(c - c') := by
        have k1 : S.b * (e₁ * x₀ * e₁) = e₁ * (S.b * x₀) * e₁ := by
          rw [← mul_assoc, ← mul_assoc, ← he₁b, mul_assoc e₁ S.b x₀]
        have k2 : (e₁ * x₀ * e₁) * S.b = e₁ * (x₀ * S.b) * e₁ := by
          rw [mul_assoc (e₁ * x₀) e₁ S.b, he₁b, ← mul_assoc, mul_assoc e₁ x₀ S.b]
        have h1 : S.b * u - u * S.b = -(e₁ * (S.b * x₀ - x₀ * S.b) * e₁) := by
          rw [hu, neg_mul, mul_neg, sub_neg_eq_add, k1, k2]
          noncomm_ring
        rw [h1, hx₀z, show c - c' = -a by rw [hc']; abel, mul_neg, neg_mul, hea]
      obtain ⟨g₀, hg₀val, hg₀N, hg₀⟩ := exists_conj_twist_character_of_adjoint S h0 hs q i hin hcrit
        hψ hθ hb hc hc'P huQN hbu
      have heu : e₁ * u * e₁ = u := by
        rw [hu]
        calc e₁ * -(e₁ * x₀ * e₁) * e₁ = -((e₁ * e₁) * x₀ * (e₁ * e₁)) := by noncomm_ring
          _ = _ := by rw [he₁e₁]
      have hmr := lt_finiteCriticalDepth_of_lt S.chain S.n S.b hcrit (by omega)
      have hu0 := S.chain.endFiltration_antitone (show 0 ≤ _ by omega)
        (centralizerLattice_mul_adjointLattice_le_inf S.chain S.b hmr.le huQN).2
      exact ⟨u, heu, hu0, g₀, hg₀val, hg₀N, hg₀⟩
  obtain ⟨u, heu, hu0, g₀, hg₀val, hg₀N, hg₀⟩ := hcorrection
  have he₂u : e₂ * u = 0 := by rw [← heu, ← mul_assoc, ← mul_assoc, h₂₁, zero_mul, zero_mul]
  have he₂g₀inv : e₂ * ((g₀⁻¹ : G) : A) = e₂ := by
    have h1 : e₂ * (g₀ : A) = e₂ := by rw [hg₀val, mul_add, mul_one, he₂u, add_zero]
    calc e₂ * ((g₀⁻¹ : G) : A) = e₂ * (g₀ : A) * ((g₀⁻¹ : G) : A) := by rw [h1]
      _ = e₂ := by rw [mul_assoc, Units.mul_inv, mul_one]
  have he₁u : e₁ * u = u := by rw [← heu, ← mul_assoc, ← mul_assoc, he₁e₁]
  -- `z⁻¹ c' z = c`
  have hcdec : c = e₁ * c * e₁ + e₂ * c * e₂ := by
    calc c = (e₁ + e₂) * c * (e₁ + e₂) := by rw [hadd, one_mul, mul_one]
      _ = e₁ * c * e₁ + e₁ * c * e₂ + e₂ * c * e₁ + e₂ * c * e₂ := by noncomm_ring
      _ = _ := by rw [hc12, hc21, add_zero, add_zero]
  have hzc : (ζ' + e₂) * c' * (ζ + e₂) = c := by
    have L1 : (ζ' + e₂) * c * (ζ + e₂) = ζ' * c * ζ + e₂ * c * e₂ := by
      have h1 : ζ' * c * e₂ = 0 := by rw [← hζ'e₁, mul_assoc ζ' e₁ c, mul_assoc, hc12, mul_zero]
      have h2 : e₂ * c * ζ = 0 := by rw [← he₁ζ, ← mul_assoc, hc21, zero_mul]
      calc (ζ' + e₂) * c * (ζ + e₂) = ζ' * c * ζ + ζ' * c * e₂ + e₂ * c * ζ + e₂ * c * e₂ := by
            noncomm_ring
        _ = _ := by rw [h1, h2, add_zero, add_zero]
    have L2 : (ζ' + e₂) * (ζ * c₁₁ * ζ') * (ζ + e₂) = c₁₁ := by
      calc (ζ' + e₂) * (ζ * c₁₁ * ζ') * (ζ + e₂) =
          (ζ' * ζ) * c₁₁ * (ζ' * ζ) + (ζ' * ζ) * c₁₁ * (ζ' * e₂) + (e₂ * ζ) * c₁₁ * (ζ' * ζ) +
            (e₂ * ζ) * c₁₁ * (ζ' * e₂) := by noncomm_ring
        _ = e₁ * c₁₁ * e₁ := by rw [hζ'ζ, hζ'e₂, he₂ζ]; noncomm_ring
        _ = (e₁ * e₁) * c * (e₁ * e₁) := by rw [hc₁₁]; noncomm_ring
        _ = c₁₁ := by rw [he₁e₁]
    have L3 : (ζ' + e₂) * c₁₁ * (ζ + e₂) = ζ' * c * ζ := by
      calc (ζ' + e₂) * c₁₁ * (ζ + e₂) = (ζ' * e₁) * c * (e₁ * ζ) + (ζ' * e₁) * c * (e₁ * e₂) +
          (e₂ * e₁) * c * (e₁ * ζ) + (e₂ * e₁) * c * (e₁ * e₂) := by rw [hc₁₁]; noncomm_ring
        _ = ζ' * c * ζ := by rw [hζ'e₁, he₁ζ, hmul, h₂₁]; noncomm_ring
    calc (ζ' + e₂) * c' * (ζ + e₂) = (ζ' + e₂) * c * (ζ + e₂) +
        (ζ' + e₂) * (ζ * c₁₁ * ζ') * (ζ + e₂) - (ζ' + e₂) * c₁₁ * (ζ + e₂) := by
          rw [hc', ha]; noncomm_ring
      _ = c := by
          rw [L1, L2, L3, hc₁₁]
          conv_rhs => rw [hcdec]
          abel
  have hform : ∀ (κ : G) (hy : g₀ * z * κ * (g₀ * z)⁻¹ ∈ simpleHGroup S.chain S.n S.b q.tail (i + 1))
      (hz : z * κ * z⁻¹ ∈ simpleHGroup S.chain S.n S.b q.tail (i + 1)),
      (ϑ ⟨_, hy⟩ : ℂ) = (θ ⟨_, hz⟩ : ℂ) * elementCharacter (traceCharacter ψF) c κ := by
    intro κ hy hz
    have hgh : g₀ * ((⟨_, hz⟩ : simpleHGroup S.chain S.n S.b q.tail (i + 1)) : G) * g₀⁻¹ ∈
        simpleHGroup S.chain S.n S.b q.tail (i + 1) := by
      have : g₀ * (z * κ * z⁻¹) * g₀⁻¹ = g₀ * z * κ * (g₀ * z)⁻¹ := by group
      change g₀ * (z * κ * z⁻¹) * g₀⁻¹ ∈ _
      rw [this]
      exact hy
    have h1 := hg₀ ⟨_, hz⟩ hgh
    have heq : g₀ * (z * κ * z⁻¹) * g₀⁻¹ = g₀ * z * κ * (g₀ * z)⁻¹ := by group
    rw [hϑ, character_congr θ heq.symm hy hgh]
    change (θ ⟨_, hgh⟩ : ℂ) * elementCharacter (traceCharacter ψF) c (g₀ * z * κ * (g₀ * z)⁻¹) = _
    rw [← heq, h1, elementCharacter_conj, hzinv, hzval, hzc]
  refine ⟨z, g₀ * z, hzval, hzinv, ?_, ?_, ?_, ?_⟩
  · intro j w hw
    have hw2 : (w : A) - 1 ∈ S.chain.endFiltration (j - 1) :=
      (Submodule.mem_toAddSubgroup _).mp hw.2
    set X := (w : A) - 1 with hX
    have hXblock : e₁ * X * e₂ = X := hw.1
    have hXe₂ : X * e₂ = X := by
      calc X * e₂ = (e₁ * X * e₂) * e₂ := by rw [hXblock]
        _ = e₁ * X * (e₂ * e₂) := by noncomm_ring
        _ = X := by rw [he₂e₂, hXblock]
    have hzX : (ζ + e₂) * X * (ζ' + e₂) = ζ * X := by
      calc (ζ + e₂) * X * (ζ' + e₂) = (ζ + e₂) * (e₁ * X * e₂) * (ζ' + e₂) := by rw [hXblock]
        _ = ((ζ + e₂) * e₁) * X * (e₂ * (ζ' + e₂)) := by noncomm_ring
        _ = ζ * X * e₂ := by
          rw [add_mul, hζe₁, h₂₁, add_zero, mul_add, he₂ζ', he₂e₂, zero_add]
        _ = ζ * X := by rw [mul_assoc, hXe₂]
    have hval : ((g₀ * z * w * (g₀ * z)⁻¹ : G) : A) - 1 = ζ * X + u * (ζ * X) := by
      have : ((g₀ * z * w * (g₀ * z)⁻¹ : G) : A) =
          (g₀ : A) * ((ζ + e₂) * (w : A) * (ζ' + e₂)) * ((g₀⁻¹ : G) : A) := by
        rw [mul_inv_rev, Units.val_mul, Units.val_mul, Units.val_mul, Units.val_mul, hzval, hzinv]
        noncomm_ring
      rw [this, show (w : A) = 1 + X by rw [hX]; abel]
      have hzz : (ζ + e₂) * (ζ' + e₂) = 1 := by rw [← hzval, ← hzinv, Units.mul_inv]
      have hg : (g₀ : A) * (ζ * X) * ((g₀⁻¹ : G) : A) = (g₀ : A) * (ζ * X) := by
        calc (g₀ : A) * (ζ * X) * ((g₀⁻¹ : G) : A) =
            (g₀ : A) * (ζ * (X * e₂)) * ((g₀⁻¹ : G) : A) := by rw [hXe₂]
          _ = (g₀ : A) * (ζ * X) * (e₂ * ((g₀⁻¹ : G) : A)) := by noncomm_ring
          _ = (g₀ : A) * (ζ * (X * e₂)) := by rw [he₂g₀inv]; noncomm_ring
          _ = (g₀ : A) * (ζ * X) := by rw [hXe₂]
      rw [show (ζ + e₂) * (1 + X) * (ζ' + e₂) = (ζ + e₂) * (ζ' + e₂) + (ζ + e₂) * X * (ζ' + e₂) by
          noncomm_ring, hzz, hzX, mul_add, add_mul, mul_one, Units.mul_inv, hg, hg₀val]
      noncomm_ring
    refine ⟨?_, ?_⟩
    · rw [hval]
      calc e₁ * (ζ * X + u * (ζ * X)) * e₂ = (e₁ * ζ) * (X * e₂) + (e₁ * u) * ζ * (X * e₂) := by
            noncomm_ring
        _ = ζ * X + u * (ζ * X) := by rw [he₁ζ, hXe₂, he₁u]; noncomm_ring
    · rw [hval]
      have h1 : ζ * X ∈ S.chain.endFiltration j := by
        simpa [show (1 : ℤ) + (j - 1) = j by ring] using S.chain.mul_mem_endFiltration hζ hw2
      exact (Submodule.mem_toAddSubgroup _).mpr
        (add_mem h1 (by simpa using S.chain.mul_mem_endFiltration hu0 h1))
  · intro κ
    have : g₀ * z * κ * (g₀ * z)⁻¹ = g₀ * (z * κ * z⁻¹) * g₀⁻¹ := by group
    rw [this]
    exact (Subgroup.mem_normalizer_iff.mp hg₀N _).symm
  · exact hform
  · intro κ hy
    have hz : z * (κ : G) * z⁻¹ ∈ simpleHGroup S.chain S.n S.b q.tail (i + 1) := by
      have := hy
      have h := (show ∀ κ : G, g₀ * z * κ * (g₀ * z)⁻¹ ∈ simpleHGroup S.chain S.n S.b q.tail (i + 1) ↔
        z * κ * z⁻¹ ∈ simpleHGroup S.chain S.n S.b q.tail (i + 1) from fun κ => by
          have : g₀ * z * κ * (g₀ * z)⁻¹ = g₀ * (z * κ * z⁻¹) * g₀⁻¹ := by group
          rw [this]
          exact (Subgroup.mem_normalizer_iff.mp hg₀N _).symm) κ
      exact h.mp hy
    apply Units.ext
    rw [hform κ hy hz, hϑ κ, simpleCharacter_conj_of_commute S h0 hs q i hin hcrit hψ hθ hzb κ hz]

end Langlands.BushnellKutzko.SplitBlocks
