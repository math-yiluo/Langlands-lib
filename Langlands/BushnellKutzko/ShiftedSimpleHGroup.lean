import Langlands.BushnellKutzko.SimpleHLayerCentralizer
import Langlands.BushnellKutzko.SimpleCharacterIntertwiningProof
import Langlands.BushnellKutzko.DiagonalSplitTypeRefinement

/-! # Shifted simple H groups and their overlap -/

noncomputable section

open ValuativeRel

namespace Langlands.BushnellKutzko.SplitBlocks

universe uF uV

variable {F : Type uF} [Field F] [ValuativeRel F] [TopologicalSpace F]
  [IsNonarchimedeanLocalField F] {V : Type uV} [AddCommGroup V] [Module F V]

local notation "A" => Module.End F V
local notation "G" => (Module.End F V)ˣ

/-- **Membership in the shifted conjugate.** For `k ∈ H^m` and the shift `z = ζ + e₂` with
`z⁻¹ = ζ' + e₂`, the conjugate `z k z⁻¹` lies in `H^m` exactly when `e₂ (k − 1) e₁ ζ' ∈ 𝔥^m`. -/
theorem shift_conj_mem_simpleHGroup_iff (S : Stratum 𝒪[F] F V) (hS0 : S.r = 0)
    (hS : S.IsSimple) (q : S.DefiningSequenceChoice) {m : ℕ} (hm : 1 ≤ m)
    {e₁ e₂ ζ ζ' : A} (he₂B : e₂ ∈ centralizerLattice S.chain S.b 0) (hζQ : ζ ∈ centralizerLattice S.chain S.b 1)
    (hζ'Q : ζ' ∈ centralizerLattice S.chain S.b (-1)) (he₁ζ' : e₁ * ζ' = ζ')
    (z : G) (hz : (z : A) = ζ + e₂) (hz' : ((z⁻¹ : G) : A) = ζ' + e₂)
    (k : G) (hk : k ∈ simpleHGroup S.chain S.n S.b q.tail m) :
    z * k * z⁻¹ ∈ simpleHGroup S.chain S.n S.b q.tail m ↔
      e₂ * ((k : A) - 1) * e₁ * ζ' ∈ simpleHLayer S.chain S.n S.b q.tail m := by
  have hn : 0 < S.n := by have := S.r_lt_n; omega
  have hprop := (sequence_for_simple S hS0 hS q).properties hn .H
  set X := simpleHLayer S.chain S.n S.b q.tail m with hX
  have hXl : X = SimpleStratumLattice.layer S.chain S.n .H S.b q.tail (m : ℤ) := rfl
  rw [simpleHGroup_mem_iff_of_pos S hS0 hS q hm] at hk
  rw [simpleHGroup_mem_iff_of_pos S hS0 hS q hm]
  set x := (k : A) - 1 with hx
  have hval : ((z * k * z⁻¹ : G) : A) - 1 = (ζ + e₂) * x * (ζ' + e₂) := by
    rw [Units.val_mul, Units.val_mul, hz, hz', ← hz, ← hz', show (k : A) = 1 + x by rw [hx]; abel,
      mul_add, mul_one, add_mul, Units.mul_inv]
    abel
  rw [hval]
  -- the three automatic blocks
  have hζxζ' : ζ * x * ζ' ∈ X := by
    have hfr := hprop.fractional m (by omega) 1
    rw [← hXl] at hfr
    have h1 : ζ * x ∈ X * centralizerLattice S.chain S.b 1 := by
      rw [← hfr]; exact Submodule.mul_mem_mul hζQ hk
    have hXQ : X * centralizerLattice S.chain S.b 0 ≤ X := by
      rw [hXl, ← hprop.fractional m (by omega) 0, ← hXl]
      exact SimpleStratumLattice.centralizer_mul_layer_le .H hprop m
    have hQQ : centralizerLattice S.chain S.b 1 * centralizerLattice S.chain S.b (-1) ≤
        centralizerLattice S.chain S.b 0 := by
      simpa using SimpleStratumLattice.centralizer_mul_le S.chain S.b 1 (-1)
    have h2 : X * centralizerLattice S.chain S.b 1 * centralizerLattice S.chain S.b (-1) ≤ X := by
      rw [mul_assoc]
      exact (mul_le_mul_right hQQ X).trans hXQ
    exact h2 (Submodule.mul_mem_mul h1 hζ'Q)
  have hζ0 : ζ ∈ centralizerLattice S.chain S.b 0 :=
    ⟨S.chain.endFiltration_antitone (by norm_num) hζQ.1, hζQ.2⟩
  have hζxe₂ : ζ * x * e₂ ∈ X :=
    (mul_mem_simpleHLayer_of_mem_centralizer S hS0 hS q m he₂B
      (mul_mem_simpleHLayer_of_mem_centralizer S hS0 hS q m hζ0 hk).1).2
  have he₂xe₂ : e₂ * x * e₂ ∈ X :=
    (mul_mem_simpleHLayer_of_mem_centralizer S hS0 hS q m he₂B
      (mul_mem_simpleHLayer_of_mem_centralizer S hS0 hS q m he₂B hk).1).2
  have hexp : (ζ + e₂) * x * (ζ' + e₂) =
      ζ * x * ζ' + ζ * x * e₂ + e₂ * x * e₁ * ζ' + e₂ * x * e₂ := by
    rw [mul_assoc (e₂ * x) e₁ ζ', he₁ζ']; noncomm_ring
  rw [hexp]
  constructor
  · intro h
    have : e₂ * x * e₁ * ζ' = (ζ * x * ζ' + ζ * x * e₂ + e₂ * x * e₁ * ζ' + e₂ * x * e₂) -
        ζ * x * ζ' - ζ * x * e₂ - e₂ * x * e₂ := by abel
    rw [this]
    exact sub_mem (sub_mem (sub_mem h hζxζ') hζxe₂) he₂xe₂
  · intro h
    exact add_mem (add_mem (add_mem hζxζ' hζxe₂) h) he₂xe₂

omit [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F] in
/-- The shift removes the left factor `ζ'` from an upper block unit. -/
theorem shift_conj_blockUnit {e₁ e₂ ζ ζ' : A} (h₂₁ : e₂ * e₁ = 0)
    (he₂ : e₂ * e₂ = e₂) (hζζ' : ζ * ζ' = e₁) (he₁ζ' : e₁ * ζ' = ζ')
    (z : G) (hz : (z : A) = ζ + e₂) (hz' : (↑z⁻¹ : A) = ζ' + e₂) (y : A) :
    z * blockUnit e₁ e₂ h₂₁ (ζ' * y) * z⁻¹ = blockUnit e₁ e₂ h₂₁ y := by
  have he₂ζ' : e₂ * ζ' = 0 := by
    calc
      _ = (e₂ * e₁) * ζ' := by rw [mul_assoc, he₁ζ']
      _ = 0 := by rw [h₂₁, zero_mul]
  have hfirst : (z : A) * e₁ * ζ' = e₁ := by
    rw [mul_assoc, he₁ζ', hz, add_mul, hζζ', he₂ζ', add_zero]
  have hsecond : e₂ * (↑z⁻¹ : A) = e₂ := by
    rw [hz', mul_add, he₂ζ', he₂, zero_add]
  apply Units.ext
  simp only [Units.val_mul, blockUnit_val, mul_add, add_mul, mul_one, Units.mul_inv]
  rw [show (z : A) * (e₁ * (ζ' * y) * e₂) * (↑z⁻¹ : A) =
    ((z : A) * e₁ * ζ') * y * (e₂ * (↑z⁻¹ : A)) by noncomm_ring, hfirst, hsecond]

/-- A unit commuting with `β` preserves a simple character wherever both sides are defined
(the centralizer case of BK93 (3.3.2)). The covariance calculation has zero trace twist. -/
theorem simpleCharacter_conj_of_commute (S : Stratum 𝒪[F] F V) (h0 : S.r = 0) (hs : S.IsSimple)
    (q : S.DefiningSequenceChoice) (i : ℕ) (hin : (i : ℤ) + 1 < S.n)
    (hcrit : (((i + 1 : ℕ) : ℤ) : WithTop ℤ) < simpleCriticalDepth S.chain S.b)
    {ψF : AddChar F ℂ} (hψ : IsBKAdditiveCharacter ψF)
    {θ : simpleHGroup S.chain S.n S.b q.tail (i + 1) →* ℂˣ}
    (hθ : θ ∈ simpleCharacters ψF S.chain S.n S.b q.tail i) {z : G}
    (hz : (z : A) * S.b = S.b * (z : A)) (h : simpleHGroup S.chain S.n S.b q.tail (i + 1))
    (hzh : z * (h : G) * z⁻¹ ∈ simpleHGroup S.chain S.n S.b q.tail (i + 1)) :
    θ ⟨_, hzh⟩ = θ h := by
  have hcrit_i : ((i : ℤ) : WithTop ℤ) < simpleCriticalDepth S.chain S.b :=
    lt_of_le_of_lt (WithTop.coe_le_coe.mpr (by push_cast; omega)) hcrit
  have hzB : z ∈ centralizerUnitGroup S.b := hz.symm
  have hcov := simpleCharacterCovariance F V ψF hψ S h0 hs q i (i + 1) (by omega) hin hcrit_i hcrit
    (by omega) θ hθ z ⟨1 * z, Set.mul_mem_mul (one_mem_simpleCharacterIntertwiningFactor S q _)
      hzB, 1, one_mem_simpleCharacterIntertwiningFactor S q _, mul_one _⟩
  apply Units.ext
  rw [hcov h hzh]
  have h1 : (↑z⁻¹ : A) * S.b * (z : A) - S.b = 0 := by
    rw [mul_assoc, ← hz, ← mul_assoc, Units.inv_mul, one_mul, sub_self]
  rw [h1, elementCharacter_apply, zero_mul, AddChar.map_zero_eq_one, mul_one]

end Langlands.BushnellKutzko.SplitBlocks
