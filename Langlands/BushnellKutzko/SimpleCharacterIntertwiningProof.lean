import Langlands.BushnellKutzko.SimpleCharacterIntertwiningInduction

/-! # Intertwining and normalizer of a simple character -/

noncomputable section

open ValuativeRel
open scoped Pointwise Classical

namespace Langlands.BushnellKutzko

universe uF uV

variable {F : Type uF} [Field F] [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F]
  {V : Type uV} [AddCommGroup V] [Module F V]

local notation "O" => 𝒪[F]
local notation "A" => Module.End F V
local notation "G" => Aˣ
local notation "Q" => centralizerLattice
local notation "J[" S "," q "]" => simpleJGroup (Stratum.chain S) (Stratum.n S) (Stratum.b S)
  (Stratum.DefiningSequenceChoice.tail q)
local notation "H[" S "," q "]" => simpleHGroup (Stratum.chain S) (Stratum.n S) (Stratum.b S)
  (Stratum.DefiningSequenceChoice.tail q)
local notation "Hₗ[" S "," q "]" => simpleHLayer (Stratum.chain S) (Stratum.n S) (Stratum.b S)
  (Stratum.DefiningSequenceChoice.tail q)
local notation "C[" ψ "," S "," q "]" => simpleCharacters ψ (Stratum.chain S) (Stratum.n S) (Stratum.b S)
  (Stratum.DefiningSequenceChoice.tail q)

private theorem outerSubgroup_le_domain_normalizer
    (S : Stratum O F V) (hS0 : S.r = 0) (hS : S.IsSimple) (q : S.DefiningSequenceChoice)
    {r m : ℕ} (hcrit : criticalExponent S.chain S.b = ((-(r : ℤ) : ℤ) : WithBot ℤ)) (hmr : m < r) :
    simpleCharacterIntertwiningSubgroup S q r m hmr ≤ Subgroup.normalizer (H[S,q] (m + 1) : Set G) := by
  have hJ : J[S,q] ((r + 1) / 2) ≤ Subgroup.normalizer (H[S,q] (m + 1) : Set G) :=
    (simpleJGroup_antitone _ _ _ _ (Nat.zero_le _)).trans ((simpleStratumGroupProperties F V S hS0 hS q).2.2.2.1 m).2.2
  rcases le_or_gt m (r / 2) with hm | hm
  · rw [simpleCharacterIntertwiningSubgroup_eq_cutoffJ_of_le S hS0 hS q hcrit hmr hm]
    exact hJ
  · have hN := ((sequence_for_simple S hS0 hS q).properties (by have := S.r_lt_n; omega) .H).adjoint
      (r : ℤ) (by omega) hcrit.le (m + 1 : ℕ) (by change (r : ℤ) / 2 + 1 ≤ _; omega)
    have hH (u : G) : u ∈ H[S,q] (m + 1) ↔ (u : A) - 1 ∈ Hₗ[S,q] (m + 1) :=
      simpleHGroup_mem_iff_of_pos S hS0 hS q (by omega)
    exact sup_le (mixedAdjointUnitGroup_le_normalizer_of_adjoint_bimodule S.chain S.b
      (show 1 ≤ r - m by omega) (-(r : ℤ)) _ _ hH hN.1 hN.2) hJ

private theorem centralizer_inf_domainNormalizer_eq
    (S : Stratum O F V) (hS0 : S.r = 0) (hS : S.IsSimple) (q : S.DefiningSequenceChoice) (m : ℕ) :
    centralizerUnitGroup S.b ⊓ Subgroup.normalizer (H[S,q] (m + 1) : Set G) =
      relativeOrderNormalizer S.chain S.b := by
  let L := S.chain
  let b := S.b
  let H := H[S,q] (m + 1)
  let B := centralizerUnitGroup b
  let K := relativeOrderNormalizer L b
  have hRel : B ⊓ H = relativeUnitFiltration L b (m + 1) := by
    refine inf_le_inf_left _ (simpleHGroup_le_unitFiltration _ _ _ _ _) |>.antisymm ?_
    exact le_inf inf_le_left (relativeUnitFiltration_le_simpleHGroup _ _ _ _ _)
  refine le_antisymm ?_ (le_inf inf_le_left ((simpleStratumGroupProperties F V S hS0 hS q).2.2.1 (m + 1)).1)
  intro g hg
  have hg' : g ∈ Subgroup.normalizer (B : Set G) ⊓ Subgroup.normalizer (H : Set G) :=
    ⟨B.le_normalizer hg.1, hg.2⟩
  have hR : g ∈ Subgroup.normalizer (relativeUnitFiltration L b (m + 1) : Set G) :=
    (congrArg (fun U : Subgroup G => Subgroup.normalizer (U : Set G)) hRel) ▸
      Subgroup.inf_normalizer_le_normalizer_inf hg'
  exact mem_relativeOrderNormalizer_of_normalizes_relativeUnits S hS.1 (m + 1) hg.1 hR

private theorem relativeOrderNormalizer_le_outerSubgroup_normalizer

    (S : Stratum O F V) (hS0 : S.r = 0) (hS : S.IsSimple) (q : S.DefiningSequenceChoice)
    {r m : ℕ} (hmr : m < r) :
    relativeOrderNormalizer S.chain S.b ≤ Subgroup.normalizer (simpleCharacterIntertwiningSubgroup S q r m hmr : Set G) := by
  let L := S.chain
  let b := S.b
  let k := r - m
  let t := -(r : ℤ)
  let M := mixedAdjointLattice L b (k : ℤ) t
  let X := mixedAdjointUnitGroup L b k t (by dsimp [k]; omega)
  let J := J[S,q] ((r + 1) / 2)
  let K := relativeOrderNormalizer L b
  have hInv := (sequence_for_simple S hS0 hS q).parameter.inverse
  have hM (j : ℤ) : Q L b j * M = M * Q L b j := by
    unfold M
    rw [centralizerLattice_mul_mixedAdjointLattice L b hInv, SimpleStratumLattice.mixed_mul_centralizer L b hInv, add_comm]
  have hM0 : M * Q L b 0 ≤ M := by
    unfold M
    rw [SimpleStratumLattice.mixed_mul_centralizer L b hInv, add_zero]
  have hX : K ≤ Subgroup.normalizer (X : Set G) := by
    apply Subgroup.le_normalizer_iff.mpr
    intro g hg x hx
    have h := (SimpleStratumLattice.conjugate_mem_iff L hM hM0 hg ((x : A) - 1)).mpr hx
    change (↑(g * x * g⁻¹) : A) - 1 ∈ M
    simpa only [Units.val_mul, mul_sub, sub_mul, mul_one, Units.mul_inv] using h
  have hJ : K ≤ Subgroup.normalizer (J : Set G) := ((simpleStratumGroupProperties F V S hS0 hS q).2.2.1 _).2
  exact (le_inf hX hJ).trans (Subgroup.inf_normalizer_le_normalizer_sup X J)

private theorem simpleCharacterNormalizer_of_intertwining

    (S : Stratum O F V) (hS0 : S.r = 0) (hS : S.IsSimple) (q : S.DefiningSequenceChoice)
    {r m : ℕ} (hr : 0 < r) (hmr : m < r)
    (hcrit : criticalExponent S.chain S.b = ((-(r : ℤ) : ℤ) : WithBot ℤ))
    (θ : H[S,q] (m + 1) →* ℂˣ)
    (hI : characterSelfIntertwining θ = simpleCharacterIntertwiningFactor S q m * (centralizerUnitGroup S.b : Set G) *
      simpleCharacterIntertwiningFactor S q m) :
    characterNormalizer θ = simpleCharacterIntertwiningFactor S q m * (relativeOrderNormalizer S.chain S.b : Set G) := by
  let Y := simpleCharacterIntertwiningSubgroup S q r m hmr
  let B := centralizerUnitGroup S.b
  let K := relativeOrderNormalizer S.chain S.b
  have hY : (Y : Set G) = simpleCharacterIntertwiningFactor S q m :=
    coe_simpleCharacterIntertwiningSubgroup S hS0 hS q hr hmr hcrit
  rw [← hY] at hI ⊢
  have hNorm := outerSubgroup_le_domain_normalizer S hS0 hS q hcrit hmr
  have hYN : Y ≤ characterNormalizerSubgroup θ := by
    intro y hy
    refine ⟨hNorm hy, ?_⟩
    rw [hI]
    exact Set.mem_mul.mpr ⟨y, Set.mem_mul.mpr ⟨y, hy, 1, one_mem B, mul_one y⟩, 1, one_mem Y, mul_one y⟩
  have hK := centralizer_inf_domainNormalizer_eq S hS0 hS q m
  have hKN : B ⊓ Subgroup.normalizer (H[S,q] (m + 1) : Set G) ≤ Subgroup.normalizer (Y : Set G) :=
    hK.symm ▸ relativeOrderNormalizer_le_outerSubgroup_normalizer S hS0 hS q hmr
  rw [characterNormalizer_eq_mul_of_doubleCoset θ Y B hI hYN hKN, hK]

/-- Bushnell–Kutzko (3.3.2) and (3.3.17), including the scalar parameter. -/
theorem simpleCharacterIntertwining : SimpleCharacterIntertwiningStatement.{uF,uV} := by
  intro F _ _ _ _ V _ _ ψF hψ S hS0 hS q m hmn hmc θ hθ
  by_cases hb : elementAlgebra S.b = ⊥
  · exact simpleCharacterIntertwining_of_scalar ψF S q hb m hθ
  · have hI := simpleCharacterSelfIntertwining ψF hψ S hS0 hS q m hmn hmc hθ
    obtain ⟨r, hr, hrn, hcrit⟩ := criticalDepth_of_simple S hS0 hS q hb
    have hmr : m < r := by
      rw [SimpleStratumLattice.simpleCriticalDepth_eq S.chain hcrit, WithTop.coe_lt_coe] at hmc
      exact_mod_cast hmc
    exact ⟨hI, simpleCharacterNormalizer_of_intertwining S hS0 hS q hr hmr hcrit θ hI⟩

/-- The conjugation formula of BK93 (3.3.9) with the outer factor evaluated
at a supplied index. The intertwining formula supplies centralizer
intertwining at the character index. -/
theorem simpleCharacterCovariance : SimpleCharacterCovarianceStatement.{uF,uV} := by
  intro F _ _ _ _ V _ _ ψF hψ S hS0 hS q m t hmn htn hmc htc hm θ hθ
  dsimp only
  intro g hg
  have hI := simpleCharacterSelfIntertwining ψF hψ S hS0 hS q m hmn hmc hθ
  exact simpleCharacter_covariance_of_centralizer_intertwining ψF hψ S hS0 hS q hmn hmc htc hm hθ
    (hI.symm ▸ centralizer_subset_simpleCharacterDoubleCoset S q m) hg

end Langlands.BushnellKutzko
