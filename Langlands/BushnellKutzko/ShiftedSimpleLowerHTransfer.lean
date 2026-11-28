import Langlands.BushnellKutzko.SimpleLowerHTransfer
import Langlands.BushnellKutzko.ShiftedLowerCornerTransfer
import Langlands.BushnellKutzko.SplitTypeRefinement

/-! # Isotypic transfer from the shifted first H group -/

noncomputable section

open ValuativeRel

namespace Langlands.BushnellKutzko.SplitBlocks

universe uF uV uW

local notation "H[" S "," q "]" => simpleHGroup (Stratum.chain S) (Stratum.n S) (Stratum.b S)
  (Stratum.DefiningSequenceChoice.tail q)
local notation "Hₗ[" S "," q "]" => simpleHLayer (Stratum.chain S) (Stratum.n S) (Stratum.b S)
  (Stratum.DefiningSequenceChoice.tail q)
local notation "Jₗ[" S "," q "]" => simpleJLayer (Stratum.chain S) (Stratum.n S) (Stratum.b S)
  (Stratum.DefiningSequenceChoice.tail q)

section

variable {F : Type uF} [Field F] [ValuativeRel F] [TopologicalSpace F]
  [IsNonarchimedeanLocalField F] {V : Type uV} [AddCommGroup V] [Module F V]

local notation "A" => Module.End F V
local notation "G" => (Module.End F V)ˣ

private theorem blockUnit_mem_normalizer_of_hOne (S : Stratum 𝒪[F] F V)
    (h0 : S.r = 0) (hs : S.IsSimple) (q : S.DefiningSequenceChoice)
    {e₁ e₂ ζ' y : A} (h₂₁ : e₂ * e₁ = 0)
    (he₂ : e₂ ∈ centralizerLattice S.chain S.b 0)
    (hζ' : ζ' ∈ centralizerLattice S.chain S.b (-1)) (he₁ζ' : e₁ * ζ' = ζ')
    (hy : y ∈ Hₗ[S,q] 1) :
    blockUnit e₁ e₂ h₂₁ (ζ' * y) ∈ Subgroup.normalizer (H[S,q] 1 : Set G) := by
  let w := e₁ * (ζ' * y) * e₂
  have hsq : w * w = 0 := by
    change e₁ * (ζ' * y) * e₂ * (e₁ * (ζ' * y) * e₂) = 0
    rw [show e₁ * (ζ' * y) * e₂ * (e₁ * (ζ' * y) * e₂) =
      e₁ * (ζ' * y) * (e₂ * e₁) * (ζ' * y) * e₂ by noncomm_ring, h₂₁]
    simp
  have hw : w = ζ' * (y * e₂) := by
    change e₁ * (ζ' * y) * e₂ = _
    rw [show e₁ * (ζ' * y) * e₂ = (e₁ * ζ') * (y * e₂) by noncomm_ring, he₁ζ']
  have hy' := (mul_mem_simpleHLayer_of_mem_centralizer S h0 hs q 1 he₂ hy).2
  have hmul (x : A) (hx : x ∈ Hₗ[S,q] 1) : w * x ∈ Hₗ[S,q] 1 ∧ x * w ∈ Hₗ[S,q] 1 := by
    exact ⟨by simpa only [hw, mul_assoc] using
      (mul_mul_mem_simpleHLayer_of_inv S h0 hs q le_rfl hζ' hy' hx).1,
      by simpa only [hw, mul_assoc] using
        (mul_mul_mem_simpleHLayer_of_inv S h0 hs q le_rfl hζ' hx hy').2.1⟩
  refine mem_normalizer_simpleHGroup_of_sq_eq_zero S h0 hs q le_rfl _ rfl hsq (fun x hx => ?_)
  obtain ⟨hl, hr⟩ := hmul x hx
  exact ⟨hl, hr, (hmul _ hl).2⟩

private theorem simpleLowerHCharacter_on_shift (S : Stratum 𝒪[F] F V)
    (h0 : S.r = 0) (hs : S.IsSimple) (q : S.DefiningSequenceChoice)
    (hn : (1 : ℤ) < S.n) (hcrit : (1 : WithTop ℤ) < simpleCriticalDepth S.chain S.b)
    {ψF : AddChar F ℂ} (hψ : IsBKAdditiveCharacter ψF)
    {θ : H[S,q] 1 →* ℂˣ} (hθ : θ ∈ simpleCharacters ψF S.chain S.n S.b q.tail 0)
    {e₁ e₂ ζ ζ' : A} (hadd : e₁ + e₂ = 1) (h₁₂ : e₁ * e₂ = 0) (h₂₁ : e₂ * e₁ = 0)
    (he₁₁ : e₁ * e₁ = e₁) (he₂₂ : e₂ * e₂ = e₂)
    (he₁ : e₁ ∈ centralizerLattice S.chain S.b 0) (he₂ : e₂ ∈ centralizerLattice S.chain S.b 0)
    (hζ : ζ ∈ centralizerLattice S.chain S.b 1) (hζ' : ζ' ∈ centralizerLattice S.chain S.b (-1))
    (he₁ζ' : e₁ * ζ' = ζ') (hζ'e₁ : ζ' * e₁ = ζ')
    (z : G) (hz : (z : A) = ζ + e₂) (hz' : (↑z⁻¹ : A) = ζ' + e₂) (hz₂ : (z : A) * e₂ = e₂)
    (η : simpleLowerHGroup S q h₁₂ →* ℂˣ)
    (hηH : ∀ h : H[S,q] 1,
      η ⟨h, (le_sup_right : H[S,q] 1 ≤ simpleLowerHGroup S q h₁₂) h.2⟩ = θ h)
    (hηD : ∀ d : simpleLowerJGroup S q h₁₂,
      η ⟨d, (le_sup_left : simpleLowerJGroup S q h₁₂ ≤ simpleLowerHGroup S q h₁₂) d.2⟩ = 1)
    (k : H[S,q] 1) (hk : e₂ * (((k : G) : A) - 1) * e₁ * ζ' ∈ Jₗ[S,q] 1) :
    ∃ hzk : z * (k : G) * z⁻¹ ∈ simpleLowerHGroup S q h₁₂, η ⟨_, hzk⟩ = θ k := by
  let H := H[S,q] 1
  let D := simpleLowerJGroup S q h₁₂
  let K := simpleLowerHGroup S q h₁₂
  let x : A := (k : G) - 1
  let d := blockUnit e₂ e₁ h₁₂ x
  have hx : x ∈ Hₗ[S,q] 1 := (simpleHGroup_mem_iff_of_pos S h0 hs q le_rfl).mp k.2
  have hdH : d ∈ H := by
    apply (simpleHGroup_mem_iff_of_pos S h0 hs q le_rfl).mpr
    change (1 + e₂ * x * e₁) - 1 ∈ Hₗ[S,q] 1
    rw [add_sub_cancel_left]
    exact (mul_mem_simpleHLayer_of_mem_centralizer S h0 hs q 1 he₁
      (mul_mem_simpleHLayer_of_mem_centralizer S h0 hs q 1 he₂ hx).1).2
  let d₀ : H := ⟨d, hdH⟩
  have hdθ : θ d₀ = 1 :=
    simpleCharacter_eq_one_of_block S h0 hs q 0 (by simpa using hn) hcrit hψ hθ
      (by rw [add_comm]; exact hadd) h₂₁ h₁₂ (commute_of_mem_centralizerLattice he₂).symm
      (commute_of_mem_centralizerLattice he₁).symm d₀ (blockUnit_mem h₁₂ he₂₂ he₁₁ x).1
  let k₀ : H := k * d₀⁻¹
  have hk₀H : z * (k₀ : G) * z⁻¹ ∈ H := by
    apply (shift_conj_mem_simpleHGroup_iff S h0 hs q le_rfl he₂ hζ hζ' he₁ζ' z hz hz' _ k₀.2).mpr
    have hcorner : e₂ * (((k₀ : G) : A) - 1) * e₁ * ζ' = -(e₂ * x * e₂) * (e₂ * x * e₁ * ζ') := by
      change e₂ * (((k : G) : A) * (↑d⁻¹ : A) - 1) * e₁ * ζ' = _
      rw [blockUnit_inv_val, show (((k : G) : A)) = 1 + x by dsimp [x]; abel]
      calc
        _ = (e₂ * x * e₁ - (e₂ * e₂) * x * (e₁ * e₁) - e₂ * x * e₂ * x * (e₁ * e₁)) * ζ' := by
          noncomm_ring
        _ = -(e₂ * x * (e₂ * e₂) * x * e₁ * ζ') := by rw [he₁₁, he₂₂]; noncomm_ring
        _ = _ := by noncomm_ring
    rw [hcorner, neg_mul]
    have hx₂ := (mul_mem_simpleHLayer_of_mem_centralizer S h0 hs q 1 he₂
      (mul_mem_simpleHLayer_of_mem_centralizer S h0 hs q 1 he₂ hx).1).2
    have hprop := simpleStratumLatticeProperties F V S h0 hs q
    have hx₂J : e₂ * x * e₂ ∈ Jₗ[S,q] 1 := (hprop.2.1.2.2.2.2.2.2.2 1).2.2 hx₂
    have hp := hprop.2.2.2.2.1.2.1 1 1 le_rfl le_rfl (Submodule.mul_mem_mul hx₂J hk)
    exact neg_mem ⟨hp.1, S.chain.endFiltration_antitone (by norm_num) hp.2⟩
  have hdD : z * d * z⁻¹ ∈ D := by
    have h₁z' : e₁ * (↑z⁻¹ : A) = ζ' := by rw [hz', mul_add, he₁ζ', h₁₂, add_zero]
    have hdval : ((z * d * z⁻¹ : G) : A) - 1 = e₂ * x * e₁ * ζ' := by
      simp only [Units.val_mul, d, blockUnit_val, mul_add, mul_one, add_mul, Units.mul_inv,
        add_sub_cancel_left]
      rw [show (z : A) * (e₂ * x * e₁) * (↑z⁻¹ : A) =
        ((z : A) * e₂) * x * (e₁ * (↑z⁻¹ : A)) by noncomm_ring,
        hz₂, h₁z', mul_assoc (e₂ * x) e₁ ζ', he₁ζ']
    change e₂ * (((z * d * z⁻¹ : G) : A) - 1) * e₁ = ((z * d * z⁻¹ : G) : A) - 1 ∧
      ((z * d * z⁻¹ : G) : A) - 1 ∈ Jₗ[S,q] 1
    rw [hdval]
    refine ⟨?_, hk⟩
    calc
      _ = (e₂ * e₂) * x * e₁ * (ζ' * e₁) := by noncomm_ring
      _ = _ := by rw [he₂₂, hζ'e₁]
  let h' : H := ⟨_, hk₀H⟩
  let d' : D := ⟨_, hdD⟩
  let k' : K := (⟨h', (le_sup_right : H ≤ K) h'.2⟩ : K) * ⟨d', (le_sup_left : D ≤ K) d'.2⟩
  have heq : (k' : G) = z * (k : G) * z⁻¹ := by
    change (z * ((k : G) * d⁻¹) * z⁻¹) * (z * d * z⁻¹) = _
    group
  refine ⟨heq ▸ k'.2, ?_⟩
  have hzb : (z : A) * S.b = S.b * (z : A) := by
    rw [hz, add_mul, mul_add, (commute_of_mem_centralizerLattice hζ).symm,
      (commute_of_mem_centralizerLattice he₂).symm]
  have hcov : θ h' = θ k₀ :=
    simpleCharacter_conj_of_commute S h0 hs q 0 (by simpa using hn) hcrit hψ hθ hzb k₀ hk₀H
  have hk₀θ : θ k₀ = θ k := by simp [k₀, hdθ]
  rw [show (⟨_, _⟩ : K) = k' from Subtype.ext heq.symm]
  change η ((⟨h', (le_sup_right : H ≤ K) h'.2⟩ : K) * ⟨d', (le_sup_left : D ≤ K) d'.2⟩) = θ k
  rw [map_mul, hηH, hηD, mul_one, hcov, hk₀θ]

end

/-- Isotypic transfer to the subgroup of `H^1` with deeper lower corner. -/
def ShiftedSimpleLowerHTransferStatement : Prop :=
  ∀ (F : Type uF) [Field F] [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F]
    (V : Type uV) [AddCommGroup V] [Module F V]
    (S : Stratum 𝒪[F] F V) (_h0 : S.r = 0) (_hs : S.IsSimple) (q : S.DefiningSequenceChoice)
    (ψF : AddChar F ℂ), IsBKAdditiveCharacter ψF →
    (1 : ℤ) < S.n → (1 : WithTop ℤ) < simpleCriticalDepth S.chain S.b →
    ∀ (θ : H[S,q] 1 →* ℂˣ), θ ∈ simpleCharacters ψF S.chain S.n S.b q.tail 0 →
    let A := Module.End F V
    let G := (Module.End F V)ˣ
    ∀ (e₁ e₂ ζ ζ' c : A) (hadd : e₁ + e₂ = 1) (_h₁₂ : e₁ * e₂ = 0) (h₂₁ : e₂ * e₁ = 0)
      (he₁ : e₁ ∈ centralizerLattice S.chain S.b 0) (he₂ : e₂ ∈ centralizerLattice S.chain S.b 0),
    ζ ∈ centralizerLattice S.chain S.b 1 → ζ' ∈ centralizerLattice S.chain S.b (-1) →
    ζ * ζ' = e₁ → e₁ * ζ = ζ → ζ * e₁ = ζ → e₁ * ζ' = ζ' → ζ' * e₁ = ζ' →
    Commute c e₁ → Commute c e₂ → c ∈ S.chain.endFiltration (-1) →
    ∀ z : G, (z : A) = ζ + e₂ → (↑z⁻¹ : A) = ζ' + e₂ →
    ∀ (W : Type uW) [AddCommGroup W] [Module ℂ W] (ρ : Representation ℂ G W) (M : Subgroup G),
    M ≤ blockUnipotent e₁ e₂ h₂₁ ⊤ →
    let K := lowerBlockSimpleHGroup S q hadd he₁ he₂ 1 le_rfl
    ∀ (ϑ : K →* ℂˣ),
    (∀ k : K, (ϑ k : ℂ) = (θ ⟨k, k.2.1⟩ : ℂ) * elementCharacter (traceCharacter ψF) c k) →
    ∀ v : W, (∀ h : H[S,q] 1, ρ (z⁻¹ * (h : G) * z) v =
      ((θ h : ℂ) * elementCharacter (traceCharacter ψF) c (z⁻¹ * (h : G) * z)) • v) →
    v ∉ Jacquet.relations ρ M →
    ∃ w : W, (∀ k : K, ρ k w = (ϑ k : ℂ) • w) ∧ w ∉ Jacquet.relations ρ M

set_option maxHeartbeats 1200000 in
theorem exists_isotypic_of_shiftedSimpleLowerH : ShiftedSimpleLowerHTransferStatement.{uF,uV,uW} := by
  intro F _ _ _ _ V _ _ S h0 hs q ψF hψ hn hcrit θ hθ A G e₁ e₂ ζ ζ' c hadd h₁₂ h₂₁ he₁ he₂
    hζ hζ' hζζ' he₁ζ hζe₁ he₁ζ' hζ'e₁ hc₁ hc₂ hc z hz hz' W _ _ ρ M hM K ϑ hϑ v hv hvM
  let H := H[S,q] 1
  let D := simpleLowerJGroup S q h₁₂
  let T := simpleLowerHGroup S q h₁₂
  let d := finiteCriticalDepth S.chain S.n S.b
  let I := Hₗ[S,q] (simpleHCutoff d).toNat
  let X := Jₗ[S,q] 1
  have hd : 0 < d := SimpleStratum.depth_pos S h0 hs
  have hIH : I ≤ Hₗ[S,q] 1 := by
    intro x hx
    exact ⟨hx.1, S.chain.endFiltration_antitone (by dsimp [simpleHCutoff]; omega) hx.2⟩
  have hdual : traceDualLattice ψF X =
      I.map (adjointMap 𝒪[F] S.b) ⊔ S.chain.endFiltration (1 - (1 : ℤ)) :=
    SimpleStratum.traceDualLattice_simpleJLayer S q h0 hs ψF hψ (k := 1)
      (by change (1 : ℤ) ≤ simpleJCutoff d; unfold simpleJCutoff; omega)
  have hX : Hₗ[S,q] 1 ≤ X := (simpleStratumLatticeProperties F V S h0 hs q).2.1.2.2.2.2.2.2.2 1 |>.2.2
  have he₁₁ : e₁ * e₁ = e₁ := by
    calc e₁ * e₁ = e₁ * (e₁ + e₂) := by rw [mul_add, h₁₂, add_zero]
      _ = e₁ := by rw [hadd, mul_one]
  have he₂₂ : e₂ * e₂ = e₂ := by
    calc e₂ * e₂ = (e₁ + e₂) * e₂ := by rw [add_mul, h₁₂, zero_add]
      _ = e₂ := by rw [hadd, one_mul]
  have hζ₂ : ζ * e₂ = 0 := by rw [← hζe₁, mul_assoc, h₁₂, mul_zero]
  have h₂ζ' : e₂ * ζ' = 0 := by rw [← he₁ζ', ← mul_assoc, h₂₁, zero_mul]
  have hζ'₂ : ζ' * e₂ = 0 := by rw [← hζ'e₁, mul_assoc, h₁₂, mul_zero]
  have hz₂ : (z : A) * e₂ = e₂ := by rw [hz, add_mul, hζ₂, he₂₂, zero_add]
  have hz'₂ : (↑z⁻¹ : A) * e₂ = e₂ := by rw [hz', add_mul, hζ'₂, he₂₂, zero_add]
  have h₁z : e₁ * (z : A) = (z : A) * e₁ := by
    rw [hz, mul_add, add_mul, he₁ζ, hζe₁, h₁₂, h₂₁]
  obtain ⟨η, hη⟩ := exists_simpleLowerHCharacter S h0 hs q h₁₂ hn hcrit hψ hθ hadd h₂₁ he₁ he₂
  have hηH (h : H) : η ⟨h, (le_sup_right : H ≤ T) h.2⟩ = θ h := by
    simpa only [Subgroup.coe_one, one_mul] using hη (1 : D) h
      (by rw [Subgroup.coe_one, one_mul]; exact (le_sup_right : H ≤ T) h.2)
  have hηD (a : D) : η ⟨a, (le_sup_left : D ≤ T) a.2⟩ = 1 := by
    simpa only [Subgroup.coe_one, mul_one, map_one] using hη a (1 : H)
      (by rw [Subgroup.coe_one, mul_one]; exact (le_sup_left : D ≤ T) a.2)
  let b := (z : A) * c * (↑z⁻¹ : A)
  have hb : b ∈ S.chain.endFiltration (-1) := by
    have hcross₁ : ζ * c * e₂ = 0 := by rw [mul_assoc, hc₂.eq, ← mul_assoc, hζ₂, zero_mul]
    have hcross₂ : e₂ * c * ζ' = 0 := by rw [← hc₂.eq, mul_assoc, h₂ζ', mul_zero]
    have hb' : b = ζ * c * ζ' + e₂ * c * e₂ := by
      dsimp [b]
      rw [hz, hz']
      calc
        _ = ζ * c * ζ' + ζ * c * e₂ + e₂ * c * ζ' + e₂ * c * e₂ := by noncomm_ring
        _ = _ := by rw [hcross₁, hcross₂, add_zero, add_zero]
    rw [hb']
    exact add_mem (mul_mul_mem_endFiltration S.chain hζ.1 hc hζ'.1 (by norm_num))
      (mul_mul_mem_endFiltration S.chain he₂.1 hc he₂.1 (by norm_num))
  have htrace (k : G) : elementCharacter (traceCharacter ψF) b (z * k * z⁻¹) =
      elementCharacter (traceCharacter ψF) c k := by
    rw [elementCharacter_conj, show (↑z⁻¹ : A) * b * (z : A) = c by
      dsimp [b]
      calc
        _ = ((↑z⁻¹ : A) * (z : A)) * c * ((↑z⁻¹ : A) * (z : A)) := by noncomm_ring
        _ = c := by rw [Units.inv_mul, one_mul, mul_one]]
  let χ : T →* ℂˣ := η * elementCharacterHom S.chain ψF hψ hb (by norm_num)
    ((simpleLowerHGroup_le_simpleJGroup S h0 hs q h₁₂).trans (simpleJGroup_le_unitFiltration _ _ _ _ 1))
  have hχ (k : T) : (χ k : ℂ) = (η k : ℂ) * elementCharacter (traceCharacter ψF) b (k : G) := rfl
  let M' := M.map (MulAut.conj z).toMonoidHom
  have hM' : M' ≤ blockUnipotent e₁ e₂ h₂₁ ⊤ := by
    rintro _ ⟨m, hm, rfl⟩
    refine ⟨?_, AddSubgroup.mem_top _⟩
    let x : A := (m : A) - 1
    have hx : e₁ * x * e₂ = x := (hM hm).1
    have he₂z' : e₂ * (↑z⁻¹ : A) = e₂ := by rw [hz', mul_add, h₂ζ', he₂₂, zero_add]
    change e₁ * (((z * m * z⁻¹ : G) : A) - 1) * e₂ = ((z * m * z⁻¹ : G) : A) - 1
    have hzval : ((z * m * z⁻¹ : G) : A) - 1 = (z : A) * x * (↑z⁻¹ : A) := by
      change (z : A) * (m : A) * (↑z⁻¹ : A) - 1 = _
      dsimp only [x]
      rw [mul_sub, sub_mul, mul_one, show (z : A) * (↑z⁻¹ : A) = 1 from Units.mul_inv z]
    rw [hzval]
    calc
      _ = (e₁ * (z : A)) * x * ((↑z⁻¹ : A) * e₂) := by noncomm_ring
      _ = (z : A) * (e₁ * x * e₂) := by rw [h₁z, hz'₂]; noncomm_ring
      _ = (z : A) * (e₁ * x * (e₂ * (↑z⁻¹ : A))) := by rw [he₂z']
      _ = _ := by rw [← mul_assoc (e₁ * x), hx]; noncomm_ring
  have hzM (m : G) (hm : m ∈ M) : z * m * z⁻¹ ∈ M' := ⟨m, hm, rfl⟩
  have hz'M (m : G) (hm : m ∈ M') : z⁻¹ * m * z⁻¹⁻¹ ∈ M := by
    obtain ⟨x, hx, rfl⟩ := hm
    change z⁻¹ * (z * x * z⁻¹) * z⁻¹⁻¹ ∈ M
    rwa [inv_inv, mul_assoc z⁻¹, inv_mul_cancel_right, inv_mul_cancel_left]
  have hvMz : ρ z v ∉ Jacquet.relations ρ M' := by
    intro hv'
    have hh : ρ z⁻¹ (ρ z v) ∈ Jacquet.relations ρ M :=
      Jacquet.apply_mem_relations ρ (N := M') (N' := M) z⁻¹ hz'M hv'
    rw [← Module.End.mul_apply, ← map_mul, inv_mul_cancel, map_one, Module.End.one_apply] at hh
    exact hvM hh
  have hvz (k : T) (hk : (k : G) ∈ H) : ρ (k : G) (ρ z v) = (χ k : ℂ) • ρ z v := by
    let h : H := ⟨k, hk⟩
    have hconj : z * (z⁻¹ * (h : G) * z) * z⁻¹ = (k : G) := by
      change z * (z⁻¹ * (k : G) * z) * z⁻¹ = (k : G)
      rw [mul_assoc z⁻¹ (k : G) z, mul_inv_cancel_left, mul_inv_cancel_right]
    have htrace' := htrace (z⁻¹ * (h : G) * z)
    rw [hconj] at htrace'
    calc
      ρ (k : G) (ρ z v) = ρ z (ρ (z⁻¹ * (h : G) * z) v) := by
        rw [← Module.End.mul_apply, ← Module.End.mul_apply, ← map_mul, ← map_mul]
        congr 2
        change (k : G) * z = z * (z⁻¹ * (k : G) * z)
        rw [mul_assoc z⁻¹ (k : G) z, mul_inv_cancel_left]
      _ = (χ k : ℂ) • ρ z v := by
        rw [hv h, map_smul, hχ, htrace']
        change _ = ((η ⟨h, (le_sup_right : H ≤ T) h.2⟩ : ℂ) * _) • _
        rw [hηH h]
  obtain ⟨w, hw, hwM⟩ := exists_isotypic_of_simpleLowerHCharacter F V S h0 hs q e₁ e₂
    h₁₂ h₂₁ he₁₁ he₂₂ he₁ he₂ ψF hψ θ hθ η hη b hb χ hχ W ρ M' hM' (ρ z v) hvz hvMz
  have hwMv : ρ z⁻¹ w ∉ Jacquet.relations ρ M := by
    intro hw'
    have hh : ρ z (ρ z⁻¹ w) ∈ Jacquet.relations ρ M' :=
      Jacquet.apply_mem_relations ρ (N := M) (N' := M') z hzM hw'
    rw [← Module.End.mul_apply, ← map_mul, mul_inv_cancel, map_one, Module.End.one_apply] at hh
    exact hwM hh
  have hshift (k : K) (hk : e₂ * (((k : G) : A) - 1) * e₁ * ζ' ∈ X) :
      ∃ hzk : z * (k : G) * z⁻¹ ∈ T, η ⟨_, hzk⟩ = θ ⟨k, k.2.1⟩ :=
    simpleLowerHCharacter_on_shift S h0 hs q hn hcrit hψ hθ hadd h₁₂ h₂₁ he₁₁ he₂₂ he₁ he₂ hζ hζ'
      he₁ζ' hζ'e₁ z hz hz' hz₂ η hηH hηD ⟨k, k.2.1⟩ hk
  refine exists_isotypic_of_lowerCornerKernel F V S h0 hs q ψF hψ 0 (by simpa using hn)
    (by simpa using hcrit) θ hθ e₁ e₂ ζ' c hadd h₁₂ h₂₁ he₁ he₂ hζ' hc₁ hc₂ hc
    I X (fun _ hx => (hIH hx).2) hX inf_le_right hdual W ρ M hM ϑ hϑ ?_ ?_ _ ?_ hwMv
  · intro y k hk
    exact (Subgroup.mem_normalizer_iff.mp
      (blockUnit_mem_normalizer_of_hOne S h0 hs q h₂₁ he₂ hζ' he₁ζ' (hIH y.2)) k).mp hk
  · intro y k hk hker
    let g := blockUnit e₁ e₂ h₂₁ (ζ' * (y : A))
    let g' := blockUnit e₁ e₂ h₂₁ (y : A)
    let k' : K := ⟨_, hk⟩
    have hzg : z * g * z⁻¹ = g' := shift_conj_blockUnit h₂₁ he₂₂ hζζ' he₁ζ' z hz hz' y
    have hg'H : g' ∈ H := by
      apply (simpleHGroup_mem_iff_of_pos S h0 hs q le_rfl).mpr
      change (1 + e₁ * (y : A) * e₂) - 1 ∈ Hₗ[S,q] 1
      rw [add_sub_cancel_left]
      exact (mul_mem_simpleHLayer_of_mem_centralizer S h0 hs q 1 he₂
        (mul_mem_simpleHLayer_of_mem_centralizer S h0 hs q 1 he₁ (hIH y.2)).1).2
    have hker' : e₂ * (((k' : G) : A) - 1) * e₁ * ζ' ∈ X := by
      change e₂ * (((g * (k : G) * g⁻¹ : G) : A) - 1) * e₁ * ζ' ∈ X
      rwa [blockUnit_conj_lowerCorner h₂₁]
    obtain ⟨hzk, hηzk⟩ := hshift k hker
    obtain ⟨hzk', hηzk'⟩ := hshift k' hker'
    let g₀ : T := ⟨g', (le_sup_right : H ≤ T) hg'H⟩
    let k₀ : T := ⟨_, hzk⟩
    have heq : (⟨_, hzk'⟩ : T) = g₀ * k₀ * g₀⁻¹ := by
      apply Subtype.ext
      change z * (g * (k : G) * g⁻¹) * z⁻¹ = g' * (z * (k : G) * z⁻¹) * g'⁻¹
      rw [← hzg]
      change MulAut.conj z (g * (k : G) * g⁻¹) =
        MulAut.conj z g * MulAut.conj z (k : G) * (MulAut.conj z g)⁻¹
      rw [map_mul, map_mul, map_inv]
    have hθeq : θ ⟨k', hk.1⟩ = θ ⟨k, k.2.1⟩ := by
      rw [← hηzk', ← hηzk, heq, map_mul, map_mul, map_inv, mul_comm (η g₀), mul_assoc,
        mul_inv_cancel, mul_one]
    have hyP : ζ' * (y : A) ∈ S.chain.endFiltration 0 := by
      simpa using S.chain.mul_mem_endFiltration hζ'.1 (hIH y.2).2
    have ht := blockUnit_elementCharacter_conj_eq S.chain hψ h₂₁ hc₁ hc₂ 1 hc hyP (k : G) k.2.2
    change ϑ k' = ϑ k
    apply Units.ext
    rw [hϑ k', hϑ k, hθeq]
    exact congrArg (fun t : ℂ => (θ ⟨k, k.2.1⟩ : ℂ) * t) ht
  · intro k hk
    obtain ⟨hzk, hηzk⟩ := hshift k hk
    have hwk := hw ⟨_, hzk⟩
    change ρ (z * (k : G) * z⁻¹) w = (χ ⟨_, hzk⟩ : ℂ) • w at hwk
    calc
      ρ (k : G) (ρ z⁻¹ w) = ρ z⁻¹ (ρ (z * (k : G) * z⁻¹) w) := by
        rw [← Module.End.mul_apply, ← Module.End.mul_apply, ← map_mul, ← map_mul]
        congr 2
        rw [mul_assoc z (k : G) z⁻¹, inv_mul_cancel_left]
      _ = (ϑ k : ℂ) • ρ z⁻¹ w := by
        rw [hwk, hχ, hηzk, htrace, ← hϑ k, map_smul]

end Langlands.BushnellKutzko.SplitBlocks
