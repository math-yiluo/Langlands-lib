import Langlands.BushnellKutzko.LowerCornerTransfer
import Langlands.BushnellKutzko.ShiftedSimpleHGroup
import Langlands.BushnellKutzko.SimpleHGroupSquareZero
import Langlands.BushnellKutzko.SimpleCharacterJNormalizer
import Langlands.BushnellKutzko.SimpleCharacterNormalizerRestriction

/-! # Isotypic transfer on the shifted overlap at depth at least two -/

noncomputable section

open ValuativeRel

namespace Langlands.BushnellKutzko.SplitBlocks

universe uF uV uW

local notation "H[" S "," q "]" => simpleHGroup (Stratum.chain S) (Stratum.n S) (Stratum.b S)
  (Stratum.DefiningSequenceChoice.tail q)
local notation "Hₗ[" S "," q "]" => simpleHLayer (Stratum.chain S) (Stratum.n S) (Stratum.b S)
  (Stratum.DefiningSequenceChoice.tail q)
local notation "J[" S "," q "]" => simpleJGroup (Stratum.chain S) (Stratum.n S) (Stratum.b S)
  (Stratum.DefiningSequenceChoice.tail q)
local notation "Jₗ[" S "," q "]" => simpleJLayer (Stratum.chain S) (Stratum.n S) (Stratum.b S)
  (Stratum.DefiningSequenceChoice.tail q)

section

variable {F : Type uF} [Field F] [ValuativeRel F] [TopologicalSpace F]
  [IsNonarchimedeanLocalField F] {V : Type uV} [AddCommGroup V] [Module F V]

local notation "A" => Module.End F V
local notation "G" => (Module.End F V)ˣ

/-- The first J layer is stable under the integral centralizer on both sides. -/
theorem mul_mem_simpleJLayer_one_of_mem_centralizer (S : Stratum 𝒪[F] F V) (h0 : S.r = 0)
    (hs : S.IsSimple) (q : S.DefiningSequenceChoice) {e x : A}
    (he : e ∈ centralizerLattice S.chain S.b 0) (hx : x ∈ Jₗ[S,q] 1) :
    e * x ∈ Jₗ[S,q] 1 ∧ x * e ∈ Jₗ[S,q] 1 := by
  have hn : 0 < S.n := by have := S.r_lt_n; omega
  have hprop := ((sequence_for_simple S h0 hs q).properties hn .J)
  let Q := centralizerLattice S.chain S.b
  have hleft : Q 0 * Jₗ[S,q] 1 ≤ Jₗ[S,q] 1 :=
    SimpleStratumLattice.centralizer_mul_layer_le .J hprop 1
  have hQ : Q 0 * Jₗ[S,q] 1 = Jₗ[S,q] 1 * Q 0 := hprop.fractional 1 (by omega) 0
  have hright : Jₗ[S,q] 1 * Q 0 ≤ Jₗ[S,q] 1 := by
    rw [← hQ]
    exact hleft
  exact ⟨hleft (Submodule.mul_mem_mul he hx), hright (Submodule.mul_mem_mul hx he)⟩

/-- Upper block units from `𝔔⁻¹ 𝔧¹` normalize `H^m` for `m ≥ 2`. -/
theorem blockUnit_mem_normalizer_of_jOne (S : Stratum 𝒪[F] F V) (h0 : S.r = 0)
    (hs : S.IsSimple) (q : S.DefiningSequenceChoice) {m : ℕ} (hm : 2 ≤ m)
    {e₁ e₂ ζ' y : A} (h₂₁ : e₂ * e₁ = 0)
    (he₁ : e₁ ∈ centralizerLattice S.chain S.b 0) (he₂ : e₂ ∈ centralizerLattice S.chain S.b 0)
    (hζ' : ζ' ∈ centralizerLattice S.chain S.b (-1)) (hy : y ∈ Jₗ[S,q] 1) :
    blockUnit e₁ e₂ h₂₁ (ζ' * y) ∈ Subgroup.normalizer (H[S,q] m : Set G) := by
  have hn : 0 < S.n := by have := S.r_lt_n; omega
  have hseq := sequence_for_simple S h0 hs q
  have hHp := hseq.properties hn .H
  have hJp := hseq.properties hn .J
  let X := Hₗ[S,q] m
  let Y := Jₗ[S,q] 1
  let Q := centralizerLattice S.chain S.b
  let w := e₁ * (ζ' * y) * e₂
  have hw : w * w = 0 := by
    dsimp [w]
    rw [show e₁ * (ζ' * y) * e₂ * (e₁ * (ζ' * y) * e₂) =
      e₁ * (ζ' * y) * (e₂ * e₁) * (ζ' * y) * e₂ by noncomm_ring, h₂₁]
    simp
  have hQY : Q (-1) * Y = Y * Q (-1) := hJp.fractional 1 (by omega) (-1)
  have hwQY : w ∈ Q (-1) * Y := by
    have hζ : e₁ * ζ' ∈ Q (-1) := by
      apply (show Q 0 * Q (-1) ≤ Q (-1) by
        simpa [Q] using SimpleStratumLattice.centralizer_mul_le S.chain S.b 0 (-1))
      exact Submodule.mul_mem_mul he₁ hζ'
    change e₁ * (ζ' * y) * e₂ ∈ Q (-1) * Y
    rw [show e₁ * (ζ' * y) * e₂ = (e₁ * ζ') * (y * e₂) by noncomm_ring]
    exact Submodule.mul_mem_mul hζ (mul_mem_simpleJLayer_one_of_mem_centralizer S h0 hs q he₂ hy).2
  have hm' : (2 : ℤ) ≤ m := by exact_mod_cast hm
  have hmix : Y * X ≤ Q 1 * X ∧ X * Y ≤ Q 1 * X :=
    hseq.jOne_mul_hLayer_le hn m hm'
  have hQX : Q 0 * X ≤ X := SimpleStratumLattice.centralizer_mul_layer_le .H hHp m
  have hQX1 : Q 1 * X = X * Q 1 := hHp.fractional m (by omega) 1
  have hQX0 : Q 0 * X = X * Q 0 := hHp.fractional m (by omega) 0
  have hleft : Q (-1) * Y * X ≤ X := by
    rw [mul_assoc]
    calc
      _ ≤ Q (-1) * (Q 1 * X) := mul_le_mul_right hmix.1 _
      _ = Q (-1) * Q 1 * X := (mul_assoc _ _ _).symm
      _ ≤ Q 0 * X := mul_le_mul_left (by
        simpa [Q] using SimpleStratumLattice.centralizer_mul_le S.chain S.b (-1) 1) _
      _ ≤ X := hQX
  have hright : X * (Y * Q (-1)) ≤ X := by
    rw [← mul_assoc]
    calc
      _ ≤ Q 1 * X * Q (-1) := mul_le_mul_left hmix.2 _
      _ = X * (Q 1 * Q (-1)) := by rw [hQX1, mul_assoc]
      _ ≤ X * Q 0 := mul_le_mul_right (by
        simpa [Q] using SimpleStratumLattice.centralizer_mul_le S.chain S.b 1 (-1)) _
      _ ≤ X := hQX0 ▸ hQX
  have hmul (x : A) (hx : x ∈ X) : w * x ∈ X ∧ x * w ∈ X :=
    ⟨hleft (Submodule.mul_mem_mul hwQY hx), hright (Submodule.mul_mem_mul hx (hQY ▸ hwQY))⟩
  refine mem_normalizer_simpleHGroup_of_sq_eq_zero S h0 hs q (by omega)
    (blockUnit e₁ e₂ h₂₁ (ζ' * y)) rfl hw (fun x hx => ?_)
  obtain ⟨hl, hr⟩ := hmul x hx
  exact ⟨hl, hr, (hmul _ hl).2⟩

end

/-- The shifted overlap transfers to the subgroup with deeper lower corner
for simple characters of positive index. -/
def ShiftedLowerCornerTransferStatement : Prop :=
  ∀ (F : Type uF) [Field F] [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F]
    (V : Type uV) [AddCommGroup V] [Module F V]
    (S : Stratum 𝒪[F] F V) (_h0 : S.r = 0) (_hs : S.IsSimple) (q : S.DefiningSequenceChoice)
    (ψF : AddChar F ℂ), IsBKAdditiveCharacter ψF →
    ∀ (i : ℕ), let m := i + 1
    2 ≤ m → (m : ℤ) < S.n → ((m : ℤ) : WithTop ℤ) < simpleCriticalDepth S.chain S.b →
    ∀ (θ : H[S,q] m →* ℂˣ), θ ∈ simpleCharacters ψF S.chain S.n S.b q.tail i →
    ∀ (e₁ e₂ ζ ζ' c : Module.End F V) (hadd : e₁ + e₂ = 1) (_h₁₂ : e₁ * e₂ = 0) (h₂₁ : e₂ * e₁ = 0)
      (he₁ : e₁ ∈ centralizerLattice S.chain S.b 0) (he₂ : e₂ ∈ centralizerLattice S.chain S.b 0),
    ζ ∈ centralizerLattice S.chain S.b 1 → ζ' ∈ centralizerLattice S.chain S.b (-1) →
    ζ * ζ' = e₁ → e₁ * ζ' = ζ' →
    Commute c e₁ → Commute c e₂ → c ∈ S.chain.endFiltration (-(m : ℤ)) →
    ∀ z : (Module.End F V)ˣ, (z : Module.End F V) = ζ + e₂ → (↑z⁻¹ : Module.End F V) = ζ' + e₂ →
    ∀ (W : Type uW) [AddCommGroup W] [Module ℂ W]
      (ρ : Representation ℂ (Module.End F V)ˣ W) (M : Subgroup (Module.End F V)ˣ),
    M ≤ blockUnipotent e₁ e₂ h₂₁ ⊤ →
    let K := lowerBlockSimpleHGroup S q hadd he₁ he₂ m (Nat.succ_pos i)
    ∀ (ϑ : K →* ℂˣ),
    (∀ k : K, (ϑ k : ℂ) = (θ ⟨k, k.2.1⟩ : ℂ) * elementCharacter (traceCharacter ψF) c k) →
    ∀ v : W,
    (∀ k : K, z * (k : (Module.End F V)ˣ) * z⁻¹ ∈ H[S,q] m → ρ k v = (ϑ k : ℂ) • v) →
    v ∉ Jacquet.relations ρ M →
    ∃ w : W, (∀ k : K, ρ k w = (ϑ k : ℂ) • w) ∧ w ∉ Jacquet.relations ρ M

set_option maxHeartbeats 900000 in
theorem exists_isotypic_of_shiftedHOverlap : ShiftedLowerCornerTransferStatement.{uF,uV,uW} := by
  intro F _ _ _ _ V _ _ S h0 hs q ψF hψ i m hm hn hcrit θ hθ e₁ e₂ ζ ζ' c hadd h₁₂ h₂₁ he₁ he₂
    hζ hζ' hζζ' he₁ζ' hc₁ hc₂ hc z hz hz' W _ _ ρ M hM K ϑ hϑ v hv hvM
  let A := Module.End F V
  let G := (Module.End F V)ˣ
  let j := (simpleJCutoff (finiteCriticalDepth S.chain S.n S.b)).toNat
  let I := Jₗ[S,q] j
  let X := Hₗ[S,q] m
  have hm1 : 1 ≤ m := by omega
  have hj : 1 ≤ j := by
    have hr := lt_finiteCriticalDepth_of_lt S.chain S.n S.b hcrit hn
    dsimp [j, simpleJCutoff]
    omega
  have hI : I ≤ Jₗ[S,q] 1 := fun y hy => ⟨hy.1, S.chain.endFiltration_antitone (by omega) hy.2⟩
  have hn0 : 0 < S.n := by have := S.r_lt_n; omega
  have hdual : traceDualLattice ψF X = I.map (adjointMap 𝒪[F] S.b) ⊔ S.chain.endFiltration (1 - (m : ℤ)) := by
    dsimp [I, X, m, j]
    rw [(sequence_for_simple S h0 hs q).traceDual_simpleHLayer hn0 ψF hψ i]
    congr 2
    omega
  have hzH (k : G) (hk : k ∈ H[S,q] m) :
      z * k * z⁻¹ ∈ H[S,q] m ↔ e₂ * ((k : A) - 1) * e₁ * ζ' ∈ X :=
    shift_conj_mem_simpleHGroup_iff S h0 hs q hm1 he₂ hζ hζ' he₁ζ' z hz hz' k hk
  have he₂₂ : e₂ * e₂ = e₂ := by
    calc
      _ = (e₁ + e₂) * e₂ := by rw [add_mul, h₁₂, zero_add]
      _ = e₂ := by rw [hadd, one_mul]
  have hzb : (z : A) * S.b = S.b * (z : A) := by
    rw [hz, add_mul, mul_add, (commute_of_mem_centralizerLattice hζ).symm,
      (commute_of_mem_centralizerLattice he₂).symm]
  have hcrit' : ((i : ℤ) : WithTop ℤ) < simpleCriticalDepth S.chain S.b :=
    lt_of_le_of_lt (WithTop.coe_le_coe.mpr (by omega)) hcrit
  refine exists_isotypic_of_lowerCornerKernel F V S h0 hs q ψF hψ i hn hcrit θ hθ e₁ e₂ ζ' c
    hadd h₁₂ h₂₁ he₁ he₂ hζ' hc₁ hc₂ hc I X (fun y hy => (hI hy).2) le_rfl inf_le_right
    hdual W ρ M hM ϑ hϑ ?_ ?_ v (fun k hk => hv k ((hzH k k.2.1).mpr hk)) hvM
  · intro y k hk
    exact (Subgroup.mem_normalizer_iff.mp
      (blockUnit_mem_normalizer_of_jOne S h0 hs q hm h₂₁ he₁ he₂ hζ' (hI y.2)) k).mp hk
  · intro y k hk hker
    let g := blockUnit e₁ e₂ h₂₁ (ζ' * (y : A))
    let g' := blockUnit e₁ e₂ h₂₁ (y : A)
    let k' : K := ⟨_, hk⟩
    have hconj : z * g * z⁻¹ = g' := shift_conj_blockUnit h₂₁ he₂₂ hζζ' he₁ζ' z hz hz' y
    have hk'z : z * (k' : G) * z⁻¹ ∈ H[S,q] m := by
      apply (hzH _ hk.1).mpr
      change e₂ * (((g * (k : G) * g⁻¹ : G) : A) - 1) * e₁ * ζ' ∈ X
      rw [blockUnit_conj_lowerCorner h₂₁]
      exact hker
    have hkz := (hzH k k.2.1).mpr hker
    have hgJ : g' ∈ J[S,q] 1 := by
      apply (simpleJGroup_mem_iff_of_pos S h0 hs q le_rfl).mpr
      change (1 + e₁ * (y : A) * e₂) - 1 ∈ Jₗ[S,q] 1
      rw [add_sub_cancel_left]
      exact (mul_mem_simpleJLayer_one_of_mem_centralizer S h0 hs q he₂
        (mul_mem_simpleJLayer_one_of_mem_centralizer S h0 hs q he₁ (hI y.2)).1).2
    have hgn : g' ∈ characterNormalizer θ :=
      simpleJ_le_characterNormalizerSubgroup ψF hψ S h0 hs q i (by omega) hcrit' hθ
        (simpleJGroup_antitone _ _ _ _ (Nat.zero_le 1) hgJ)
    have hzgk : g' * (z * (k : G) * z⁻¹) * g'⁻¹ = z * (k' : G) * z⁻¹ := by
      change g' * (z * (k : G) * z⁻¹) * g'⁻¹ = z * (g * (k : G) * g⁻¹) * z⁻¹
      rw [← hconj]
      group
    have hθg : θ ⟨_, hk'z⟩ = θ ⟨_, hkz⟩ :=
      (congrArg θ (Subtype.ext hzgk.symm)).trans (hgn.2 ⟨_, hkz⟩ (hzgk.symm ▸ hk'z))
    have hθ₁ := simpleCharacter_conj_of_commute S h0 hs q i (by omega) hcrit hψ hθ hzb ⟨k, k.2.1⟩ hkz
    have hθ₂ := simpleCharacter_conj_of_commute S h0 hs q i (by omega) hcrit hψ hθ hzb ⟨k', hk.1⟩ hk'z
    have hyP : ζ' * (y : A) ∈ S.chain.endFiltration 0 := by
      simpa using S.chain.mul_mem_endFiltration hζ'.1 (hI y.2).2
    have ht := blockUnit_elementCharacter_conj_eq S.chain hψ h₂₁ hc₁ hc₂ (m : ℤ) hc hyP (k : G) k.2.2
    change ϑ k' = ϑ k
    apply Units.ext
    rw [hϑ k', hϑ k, ← hθ₂, hθg, hθ₁]
    exact congrArg (fun t : ℂ => (θ ⟨k, k.2.1⟩ : ℂ) * t) ht

end Langlands.BushnellKutzko.SplitBlocks
