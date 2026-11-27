import Langlands.BushnellKutzko.SimpleCharacterCovarianceCalculation
import Langlands.BushnellKutzko.SimpleCharacterFormalIntertwining
import Langlands.BushnellKutzko.SimpleCharacterJNormalizer

/-! # The simple-character conjugation formula on the outer double coset -/

noncomputable section

open ValuativeRel
open scoped Pointwise Classical

namespace Langlands.BushnellKutzko

universe uF uV

variable {F : Type uF} [Field F] [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F]
  {V : Type uV} [AddCommGroup V] [Module F V]

local notation "O" => 𝒪[F]
local notation "A" => Module.End F V
local notation "G" => (Module.End F V)ˣ
local notation "J[" S "," q "]" => simpleJGroup (Stratum.chain S) (Stratum.n S) (Stratum.b S)
  (Stratum.DefiningSequenceChoice.tail q)
local notation "H[" S "," q "]" => simpleHGroup (Stratum.chain S) (Stratum.n S) (Stratum.b S)
  (Stratum.DefiningSequenceChoice.tail q)
local notation "Jₗ[" S "," q "]" => simpleJLayer (Stratum.chain S) (Stratum.n S) (Stratum.b S)
  (Stratum.DefiningSequenceChoice.tail q)
local notation "Hₗ[" S "," q "]" => simpleHLayer (Stratum.chain S) (Stratum.n S) (Stratum.b S)
  (Stratum.DefiningSequenceChoice.tail q)
local notation "C[" ψ "," S "," q "]" => simpleCharacters ψ (Stratum.chain S) (Stratum.n S) (Stratum.b S)
  (Stratum.DefiningSequenceChoice.tail q)

/-- The conjugation difference of the parameter for a cutoff J unit belongs
to the trace dual of the character domain lattice. Together with J invariance
this gives the covariance identity. -/
theorem simpleCharacter_cutoffJ_conjugationRatio
    (ψF : AddChar F ℂ) (hψ : IsBKAdditiveCharacter ψF)
    (S : Stratum O F V) (hS0 : S.r = 0) (hS : S.IsSimple) (q : S.DefiningSequenceChoice)
    {r m : ℕ} (hr : 0 < r) (hcrit : criticalExponent S.chain S.b = ((-(r : ℤ) : ℤ) : WithBot ℤ))
    (hmn : (m : ℤ) < S.n) (hmc : ((m : ℤ) : WithTop ℤ) < simpleCriticalDepth S.chain S.b)
    {θ : H[S,q] (m + 1) →* ℂˣ} (hθ : θ ∈ C[ψF,S,q] m)
    {x : G} (hx : x ∈ J[S,q] ((r + 1) / 2)) :
    x ∈ Subgroup.normalizer (H[S,q] (m + 1) : Set G) ∧ characterConjugationRatio ψF S.b θ x := by
  let j := (r + 1) / 2
  have hj : 1 ≤ j := by dsimp [j]; omega
  have hxJ₀ := simpleJGroup_antitone S.chain S.n S.b q.tail (Nat.zero_le j) hx
  have hNx : x ∈ characterNormalizer θ := simpleJ_le_characterNormalizerSubgroup ψF hψ S hS0 hS q m
    hmn hmc hθ hxJ₀
  refine ⟨hNx.1, characterConjugationRatio_of_intertwining ψF S.b θ hNx.2 ?_⟩
  obtain ⟨hA, hJD, hDJ⟩ := simpleCharacterTraceDual_bimodule S hS0 hS q ψF hψ (m := m) hcrit
  have hK (x : G) : x ∈ J[S,q] j ↔ (x : A) - 1 ∈ Jₗ[S,q] j :=
    simpleJGroup_mem_iff_of_pos S hS0 hS q hj
  have hD : (↑x⁻¹ : A) * S.b * (x : A) - S.b ∈ traceDualLattice ψF (Hₗ[S,q] (m + 1)) :=
    latticeCoset_conj_sub_mem_of_adjoint_image S.b hJD hDJ hA ((hK _).mp hx)
      ((hK _).mp (inv_mem hx)) (show S.b - S.b ∈ _ by rw [sub_self]; exact zero_mem _)
  intro u
  exact hD _ ((simpleHGroup_mem_iff_of_pos S hS0 hS q (by omega)).mp u.prop)

/-- Given centralizer intertwining, the mixed-commutator calculation supplies
covariance on the whole double coset with outer factors evaluated at `t`. -/
theorem simpleCharacter_covariance_of_centralizer_intertwining
    (ψF : AddChar F ℂ) (hψ : IsBKAdditiveCharacter ψF)
    (S : Stratum O F V) (hS0 : S.r = 0) (hS : S.IsSimple) (q : S.DefiningSequenceChoice) {m t : ℕ}
    (hmn : (m : ℤ) < S.n) (hmc : ((m : ℤ) : WithTop ℤ) < simpleCriticalDepth S.chain S.b)
    (htc : ((t : ℤ) : WithTop ℤ) < simpleCriticalDepth S.chain S.b) (hm : t / 2 ≤ m)
    {θ : H[S,q] (m + 1) →* ℂˣ} (hθ : θ ∈ C[ψF,S,q] m)
    (hB : (centralizerUnitGroup S.b : Set G) ⊆ characterSelfIntertwining θ)
    {g : G} (hg : g ∈ simpleCharacterIntertwiningFactor S q t * (centralizerUnitGroup S.b : Set G) *
      simpleCharacterIntertwiningFactor S q t) : characterConjugationRatio ψF S.b θ g := by
  refine characterConjugationRatio_of_centralizer_doubleCoset ψF S.b θ _ ?_ hB hg
  intro y hy
  by_cases hb : elementAlgebra S.b = ⊥
  · rw [simpleCharacterIntertwiningFactor, ite_eq_left hb] at hy
    have hy' : y = 1 := hy
    subst y
    refine ⟨one_mem _, ?_⟩
    intro u hu
    simp [elementCharacter_apply]
  · obtain ⟨r, hr, hrn, hcrit⟩ := criticalDepth_of_simple S hS0 hS q hb
    have hcritDepth := SimpleStratumLattice.simpleCriticalDepth_eq S.chain hcrit
    have htr : t < r := by rw [hcritDepth, WithTop.coe_lt_coe] at htc; exact_mod_cast htc
    have hmr : m < r := by rw [hcritDepth, WithTop.coe_lt_coe] at hmc; exact_mod_cast hmc
    let j := (r + 1) / 2
    let X := mixedAdjointUnitGroup S.chain S.b (r - t) (-(r : ℤ)) (by omega)
    let K := J[S,q] j
    have hN := simpleJLayer_cutoff_adjoint_bimodule S hS0 hS q hcrit
    have hK (z : G) : z ∈ K ↔ (z : A) - 1 ∈ Jₗ[S,q] j :=
      simpleJGroup_mem_iff_of_pos S hS0 hS q (by dsimp [j]; omega)
    have hX : X ≤ Subgroup.normalizer (K : Set G) :=
      mixedAdjointUnitGroup_le_normalizer_of_adjoint_bimodule S.chain S.b (by omega) _ _ K hK hN.1 hN.2
    rw [← coe_simpleCharacterIntertwiningSubgroup S hS0 hS q hr htr hcrit] at hy
    change y ∈ ((X ⊔ K : Subgroup G) : Set G) at hy
    rw [Subgroup.coe_mul_of_left_le_normalizer_right X K hX] at hy
    obtain ⟨x, hx, z, hz, rfl⟩ := Set.mem_mul.mp hy
    let d := max m (r / 2)
    have hdc : ((d : ℤ) : WithTop ℤ) < simpleCriticalDepth S.chain S.b := by
      rw [hcritDepth, WithTop.coe_lt_coe]
      dsimp [d]
      omega
    have hθd := simpleCharacters_restrict_forward ψF S hS0 hS q (le_max_left m (r / 2))
      (by omega) hdc hθ
    have hcomm := simpleCharacterCommutatorAt ψF hψ S hS0 hS q hcrit (le_max_right m (r / 2))
      (by omega) hθd
    have hHJ := (simpleStratumGroupProperties F V S hS0 hS q).2.2.2.1 (m + 1) |>.1
    obtain ⟨hxN, hxC⟩ := simpleCharacterConjugationRatio_of_mixed S.chain ψF S.b J[S,q] htr hm _ hHJ θ hcomm hx
    obtain ⟨hzN, hzC⟩ := simpleCharacter_cutoffJ_conjugationRatio ψF hψ S hS0 hS q hr hcrit hmn hmc hθ hz
    exact ⟨mul_mem hxN hzN, characterConjugationRatio.mul_of_overlap ψF S.b θ hxC hzC
      (fun u _ => (Subgroup.mem_normalizer_iff.mp hzN (u : G)).mp u.prop)⟩

end Langlands.BushnellKutzko
