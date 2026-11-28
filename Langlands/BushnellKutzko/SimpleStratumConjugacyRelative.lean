import Langlands.BushnellKutzko.SimpleStratumConjugacyDepthOne
import Langlands.BushnellKutzko.SimpleIntertwiningProof

/-! # Relative intertwining for the induction step of BK93 (2.6.1)

Let `[𝔄,n,t,γ]` be simple and `b₁, b₂ ∈ 𝔓^{−t}`. Suppose some `g ∈ G` carries an element `y`
of `γ + b₂ + 𝔓^{1−t}` into `γ + b₁ + 𝔓^{1−t}`. By BK93 (1.5.8), `g = z₁δz₂` with `δ`
commuting with `γ` and `z₁, z₂` in the neighborhood `1 + 𝔔^{−(t+k)}𝔑_k` of (1.5.8). With
`w = z₁⁻¹yz₁` and `[γ,z] = γz − zγ`, this factorization gives the two congruences
`w ≡ γ + [γ,z₁] + b₂` and `δ⁻¹wδ ≡ γ − [γ,z₂] + b₁` modulo `𝔓^{1−t}`
(`exists_centralizer_intertwining`). This is the first computation in the induction step
of the proof of BK93 (2.6.1), printed pp. 84–85.

Applying a tame corestriction to these congruences, which shows that `δ` intertwines the
derived cosets, is done in `SimpleStratumConjugacyStep`. The scalar case of `PureOrNull` is
`pureOrNull_of_scalar` in `SimpleStratumConjugacyDepthOne`.
-/

noncomputable section

open ValuativeRel

namespace Langlands.BushnellKutzko.SimpleConjugacy

open CriticalDerived

universe uF uV

section Neighborhood

variable {F : Type uF} [Field F] [ValuativeRel F] {V : Type uV} [AddCommGroup V] [Module F V]

local notation "A" => Module.End F V

/-- An element of the factor `1 + 𝔔^{−(t+k)}𝔑_k` of BK93 (1.5.8) is congruent to `1` modulo
`𝔓`, and its commutator with `γ` lies in `𝔓^{−t}`. -/
theorem neighborhood_bounds (T : Stratum 𝒪[F] F V) (hT : T.IsSimple)
    (w : Aˣ) (hw : w ∈ T.simpleIntertwiningNeighborhood) :
    (w : A) - 1 ∈ T.chain.endFiltration 1 ∧
      (↑w⁻¹ : A) - 1 ∈ T.chain.endFiltration 1 ∧
      T.b * (w : A) - (w : A) * T.b ∈ T.chain.endFiltration (-T.r) := by
  rcases hw with ⟨_, rfl⟩ | ⟨k, hk, hw⟩
  · simp
  have hkr : k < -T.r := WithBot.coe_lt_coe.mp (hk ▸ hT.2)
  let d := -(T.r + k)
  have hdk : d + k = -T.r := by dsimp [d]; omega
  have hprod : centralizerLattice T.chain T.b d * adjointLattice T.chain T.b k ≤
      T.chain.endFiltration d ⊓ (T.chain.endFiltration (-T.r)).comap (adjointMap 𝒪[F] T.b) := by
    rw [Submodule.mul_le]
    intro p hp q hq
    change p ∈ T.chain.endFiltration d ∧ T.b * p - p * T.b = 0 at hp
    change q ∈ T.chain.endFiltration 0 ∧ T.b * q - q * T.b ∈ T.chain.endFiltration k at hq
    change p * q ∈ T.chain.endFiltration d ∧ T.b * (p * q) - (p * q) * T.b ∈
      T.chain.endFiltration (-T.r)
    refine ⟨by simpa using T.chain.mul_mem_endFiltration hp.1 hq.1, ?_⟩
    rw [show T.b * (p * q) - (p * q) * T.b =
      (T.b * p - p * T.b) * q + p * (T.b * q - q * T.b) by noncomm_ring,
      hp.2, zero_mul, zero_add]
    simpa only [hdk] using T.chain.mul_mem_endFiltration hp.1 hq.2
  obtain ⟨hwf, hwc⟩ := hprod hw
  have hw₁ : (w : A) - 1 ∈ T.chain.endFiltration 1 :=
    T.chain.endFiltration_antitone (by dsimp [d]; omega) hwf
  obtain ⟨g, hg, hgw⟩ := T.chain.exists_mem_unitFiltration (n := 1) le_rfl hw₁
  have heq : g = w := Units.ext (by rw [hgw, add_sub_cancel])
  subst g
  refine ⟨hw₁, (T.chain.mem_unitFiltration.mp ((T.chain.unitFiltration 1).inv_mem hg)).2.2, ?_⟩
  change T.b * ((w : A) - 1) - ((w : A) - 1) * T.b ∈ T.chain.endFiltration (-T.r) at hwc
  simpa only [mul_sub, sub_mul, mul_one, one_mul, sub_sub_sub_cancel_right] using hwc

variable (𝓛 : LatticeChain 𝒪[F] F V)

local notation "P" => 𝓛.endFiltration

/-- Conjugation by `w ≡ 1 (mod 𝔓)` with `[γ,w] ∈ 𝔓^{−t}`:
`w⁻¹(γ + b)w ≡ γ + [γ,w] + b (mod 𝔓^{1−t})` for `b ∈ 𝔓^{−t}`. -/
theorem conj_inv_left {t : ℤ} {γ b : A} {w : Aˣ} (hw : (w : A) - 1 ∈ P 1)
    (hwi : (↑w⁻¹ : A) - 1 ∈ P 1) (hwa : γ * w - w * γ ∈ P (-t)) (hb : b ∈ P (-t)) :
    (↑w⁻¹ : A) * (γ + b) * w - (γ + (γ * w - w * γ) + b) ∈ P (1 - t) := by
  have hwi0 : (↑w⁻¹ : A) ∈ P 0 := by
    simpa only [sub_add_cancel] using add_mem (𝓛.endFiltration_antitone (by norm_num) hwi)
      ((𝓛.mem_order_iff_mem_endFiltration).mp (one_mem 𝓛.order))
  have key : (γ + b) * w - (w : A) * (γ + (γ * w - w * γ) + b) =
      (b * ((w : A) - 1) - ((w : A) - 1) * b) - ((w : A) - 1) * (γ * w - w * γ) := by
    noncomm_ring
  have hkey : (γ + b) * w - (w : A) * (γ + (γ * w - w * γ) + b) ∈ P (1 - t) := by
    rw [key]
    refine sub_mem (sub_mem ?_ ?_) ?_
    · simpa only [show -t + 1 = 1 - t by ring] using 𝓛.mul_mem_endFiltration hb hw
    · simpa only [show 1 + -t = 1 - t by ring] using 𝓛.mul_mem_endFiltration hw hb
    · simpa only [show 1 + -t = 1 - t by ring] using 𝓛.mul_mem_endFiltration hw hwa
  have h := 𝓛.mul_mem_endFiltration hwi0 hkey
  rw [zero_add, mul_sub, ← mul_assoc, ← mul_assoc, Units.inv_mul, one_mul] at h
  exact h

/-- Conjugation by `w ≡ 1 (mod 𝔓)` with `[γ,w] ∈ 𝔓^{−t}`:
`w(γ + b)w⁻¹ ≡ γ − [γ,w] + b (mod 𝔓^{1−t})` for `b ∈ 𝔓^{−t}`. -/
theorem conj_inv_right {t : ℤ} {γ b : A} {w : Aˣ} (hw : (w : A) - 1 ∈ P 1)
    (hwi : (↑w⁻¹ : A) - 1 ∈ P 1) (hwa : γ * w - w * γ ∈ P (-t)) (hb : b ∈ P (-t)) :
    (w : A) * (γ + b) * ↑w⁻¹ - (γ - (γ * w - w * γ) + b) ∈ P (1 - t) := by
  have hwi0 : (↑w⁻¹ : A) ∈ P 0 := by
    simpa only [sub_add_cancel] using add_mem (𝓛.endFiltration_antitone (by norm_num) hwi)
      ((𝓛.mem_order_iff_mem_endFiltration).mp (one_mem 𝓛.order))
  have key : (w : A) * (γ + b) - (γ - (γ * w - w * γ) + b) * w =
      ((w : A) - 1) * b - b * ((w : A) - 1) + (γ * w - w * γ) * ((w : A) - 1) := by
    noncomm_ring
  have hkey : (w : A) * (γ + b) - (γ - (γ * w - w * γ) + b) * w ∈ P (1 - t) := by
    rw [key]
    refine add_mem (sub_mem ?_ ?_) ?_
    · simpa only [show 1 + -t = 1 - t by ring] using 𝓛.mul_mem_endFiltration hw hb
    · simpa only [show -t + 1 = 1 - t by ring] using 𝓛.mul_mem_endFiltration hb hw
    · simpa only [show -t + 1 = 1 - t by ring] using 𝓛.mul_mem_endFiltration hwa hw
  have h := 𝓛.mul_mem_endFiltration hkey hwi0
  rw [add_zero, sub_mul, mul_assoc _ (w : A), Units.mul_inv, mul_one] at h
  exact h

end Neighborhood

section Decomposition

variable {F : Type uF} [Field F] [ValuativeRel F] [TopologicalSpace F]
  [IsNonarchimedeanLocalField F] {V : Type uV} [AddCommGroup V] [Module F V]
  [FiniteDimensional F V]

local notation "A" => Module.End F V

/-- **The intertwining computation in the proof of BK93 (2.6.1)**, printed pp. 84–85. Let
`Γ = [𝔄,n,t,γ]` be simple, `b₁, b₂ ∈ 𝔓^{−t}`, and let `g` carry an element `y` of
`γ + b₂ + 𝔓^{1−t}` into `γ + b₁ + 𝔓^{1−t}`. By BK93 (1.5.8), `g = z₁δz₂` with `δ` commuting
with `γ` and `z₁, z₂` in the neighborhood of (1.5.8). With `w = z₁⁻¹yz₁` one has
`w ≡ γ + [γ,z₁] + b₂` and `δ⁻¹wδ ≡ γ − [γ,z₂] + b₁` modulo `𝔓^{1−t}`. -/
theorem exists_centralizer_intertwining (Γ : Stratum 𝒪[F] F V) (hΓ : Γ.IsSimple)
    {b₁ b₂ y : A} {g : Aˣ} (hb₁ : b₁ ∈ Γ.chain.endFiltration (-Γ.r))
    (hb₂ : b₂ ∈ Γ.chain.endFiltration (-Γ.r))
    (hy : y - (Γ.b + b₂) ∈ Γ.chain.endFiltration (1 - Γ.r))
    (hgy : ((g⁻¹ : Aˣ) : A) * y * g - (Γ.b + b₁) ∈ Γ.chain.endFiltration (1 - Γ.r)) :
    ∃ (δ : Aˣ) (w z₁ z₂ : A), Γ.b * δ = δ * Γ.b ∧
      w - (Γ.b + (Γ.b * z₁ - z₁ * Γ.b) + b₂) ∈ Γ.chain.endFiltration (1 - Γ.r) ∧
      ((δ⁻¹ : Aˣ) : A) * w * δ - (Γ.b - (Γ.b * z₂ - z₂ * Γ.b) + b₁) ∈
        Γ.chain.endFiltration (1 - Γ.r) := by
  set 𝓛 := Γ.chain
  set t := Γ.r
  set γ := Γ.b
  have hle : 𝓛.endFiltration (1 - t) ≤ 𝓛.endFiltration (-t) :=
    𝓛.endFiltration_antitone (by omega)
  have hyΓ : y ∈ Γ.coset := by
    change y - γ ∈ 𝓛.endFiltration (-t)
    rw [show y - γ = (y - (γ + b₂)) + b₂ by abel]
    exact add_mem (hle hy) hb₂
  have hgyΓ : ((g⁻¹ : Aˣ) : A) * y * g ∈ Γ.coset := by
    change ((g⁻¹ : Aˣ) : A) * y * g - γ ∈ 𝓛.endFiltration (-t)
    rw [show ((g⁻¹ : Aˣ) : A) * y * g - γ = (((g⁻¹ : Aˣ) : A) * y * g - (γ + b₁)) + b₁ by abel]
    exact add_mem (hle hgy) hb₁
  have hg : g ∈ Γ.formalSelfIntertwining := ⟨y, hyΓ, hgyΓ⟩
  rw [simpleIntertwining F V Γ hΓ] at hg
  obtain ⟨a, ha, n₂, hn₂, rfl⟩ := Set.mem_mul.mp hg
  obtain ⟨n₁, hn₁, δ, hδ, rfl⟩ := Set.mem_mul.mp ha
  obtain ⟨h₁, h₁i, h₁a⟩ := neighborhood_bounds Γ hΓ n₁ hn₁
  obtain ⟨h₂, h₂i, h₂a⟩ := neighborhood_bounds Γ hΓ n₂ hn₂
  have hP0 {x : A} (hx : x - 1 ∈ 𝓛.endFiltration 1) : x ∈ 𝓛.endFiltration 0 := by
    simpa only [sub_add_cancel] using add_mem (𝓛.endFiltration_antitone (by norm_num) hx)
      ((𝓛.mem_order_iff_mem_endFiltration).mp (one_mem 𝓛.order))
  let w : A := ((n₁⁻¹ : Aˣ) : A) * y * n₁
  refine ⟨δ, w, n₁, n₂, hδ, ?_, ?_⟩
  · have hc := conj_inv_left 𝓛 h₁ h₁i h₁a hb₂
    have hm := 𝓛.mul_mem_endFiltration (𝓛.mul_mem_endFiltration (hP0 h₁i) hy) (hP0 h₁)
    rw [zero_add, add_zero] at hm
    have hsum := add_mem hm hc
    rw [show ((n₁⁻¹ : Aˣ) : A) * (y - (γ + b₂)) * n₁ +
        (((n₁⁻¹ : Aˣ) : A) * (γ + b₂) * n₁ - (γ + (γ * n₁ - n₁ * γ) + b₂)) =
        w - (γ + (γ * n₁ - n₁ * γ) + b₂) by simp only [w]; noncomm_ring] at hsum
    exact hsum
  · have hc := conj_inv_right 𝓛 h₂ h₂i h₂a hb₁
    have hm := 𝓛.mul_mem_endFiltration (𝓛.mul_mem_endFiltration (hP0 h₂) hgy) (hP0 h₂i)
    rw [zero_add, add_zero] at hm
    have hsum := add_mem hm hc
    have hid : ((δ⁻¹ : Aˣ) : A) * w * δ =
        (n₂ : A) * ((((n₁ * δ * n₂)⁻¹ : Aˣ) : A) * y * ↑(n₁ * δ * n₂)) * ↑n₂⁻¹ := by
      simp only [w, mul_inv_rev, Units.val_mul, mul_assoc, Units.mul_inv_cancel_left,
        Units.mul_inv, mul_one]
    rw [hid]
    rw [show (n₂ : A) * ((((n₁ * δ * n₂)⁻¹ : Aˣ) : A) * y * ↑(n₁ * δ * n₂) - (γ + b₁)) *
        ↑n₂⁻¹ + ((n₂ : A) * (γ + b₁) * ↑n₂⁻¹ - (γ - (γ * n₂ - n₂ * γ) + b₁)) =
        (n₂ : A) * ((((n₁ * δ * n₂)⁻¹ : Aˣ) : A) * y * ↑(n₁ * δ * n₂)) * ↑n₂⁻¹ -
          (γ - (γ * n₂ - n₂ * γ) + b₁) by noncomm_ring] at hsum
    exact hsum

end Decomposition

end Langlands.BushnellKutzko.SimpleConjugacy
