import Langlands.BushnellKutzko.SimpleCharacterIntertwiningHigh
import Langlands.BushnellKutzko.SimpleCharacterLowDepth

/-! # Self-intertwining at every simple-character depth -/

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
local notation "P" => LatticeChain.endFiltration
local notation "Q" => centralizerLattice
local notation "J[" S "," q "]" => simpleJGroup (Stratum.chain S) (Stratum.n S) (Stratum.b S)
  (Stratum.DefiningSequenceChoice.tail q)
local notation "H[" S "," q "]" => simpleHGroup (Stratum.chain S) (Stratum.n S) (Stratum.b S)
  (Stratum.DefiningSequenceChoice.tail q)
local notation "Hₗ[" S "," q "]" => simpleHLayer (Stratum.chain S) (Stratum.n S) (Stratum.b S)
  (Stratum.DefiningSequenceChoice.tail q)
local notation "C[" ψ "," S "," q "]" => simpleCharacters ψ (Stratum.chain S) (Stratum.n S) (Stratum.b S)
  (Stratum.DefiningSequenceChoice.tail q)
local notation "Y[" S "," q "," m "]" => simpleCharacterIntertwiningFactor S q m
local notation "B[" S "]" => (centralizerUnitGroup (Stratum.b S) : Set G)

/-- For character indices `m ≤ r / 2`, the mixed congruence group is contained
in cutoff J, so the outer group equals cutoff J. -/
theorem simpleCharacterIntertwiningSubgroup_eq_cutoffJ_of_le
    (S : Stratum O F V) (hS0 : S.r = 0) (hS : S.IsSimple)
    (q : S.DefiningSequenceChoice) {r m : ℕ} (hcrit : criticalExponent S.chain S.b = ((-(r : ℤ) : ℤ) : WithBot ℤ))
    (hmr : m < r) (hm : m ≤ r / 2) :
    simpleCharacterIntertwiningSubgroup S q r m hmr = J[S,q] ((r + 1) / 2) := by
  unfold simpleCharacterIntertwiningSubgroup
  apply sup_eq_right.mpr
  intro g hg
  apply (simpleJGroup_mem_iff_of_pos S hS0 hS q (by omega)).mpr
  exact (sequence_for_simple S hS0 hS q).mixed_le_simpleJLayer_cutoff (by have := S.r_lt_n; omega) hcrit
    (SimpleStratumLattice.mixed_antitone_left S.chain S.b (-(r : ℤ))
      (show (((r + 1) / 2 : ℕ) : ℤ) ≤ ((r - m : ℕ) : ℤ) by omega) hg)

/-- The outer factor agrees with the carrier of cutoff J in the lower range. -/
theorem simpleCharacterIntertwiningFactor_eq_cutoffJ_of_le
    (S : Stratum O F V) (hS0 : S.r = 0) (hS : S.IsSimple)
    (q : S.DefiningSequenceChoice) {r m : ℕ} (hcrit : criticalExponent S.chain S.b = ((-(r : ℤ) : ℤ) : WithBot ℤ))
    (hmr : m < r) (hm : m ≤ r / 2) : Y[S,q,m] = (J[S,q] ((r + 1) / 2) : Set G) := by
  rw [← coe_simpleCharacterIntertwiningSubgroup S hS0 hS q (by omega) hmr hcrit,
    simpleCharacterIntertwiningSubgroup_eq_cutoffJ_of_le S hS0 hS q hcrit hmr hm]

private theorem simpleCharacterIntertwining_low_of_cutoff
    (ψF : AddChar F ℂ) (hψ : IsBKAdditiveCharacter ψF)
    (S : Stratum O F V) (hS0 : S.r = 0) (hS : S.IsSimple) (q : S.DefiningSequenceChoice)
    {r m : ℕ} (hmn : (m : ℤ) < S.n) (hmr : m < r) (hm : m < r / 2)
    (hcrit : criticalExponent S.chain S.b = ((-(r : ℤ) : ℤ) : WithBot ℤ))
    {θ : H[S,q] (m + 1) →* ℂˣ} (hθ : θ ∈ C[ψF,S,q] m)
    (hI : characterSelfIntertwining (θ.comp (Subgroup.inclusion
      (simpleHGroup_antitone S.chain S.n S.b q.tail (Nat.succ_le_succ hm.le)))) =
      Y[S,q,r / 2] * B[S] * Y[S,q,r / 2]) :
    characterSelfIntertwining θ = Y[S,q,m] * B[S] * Y[S,q,m] := by
  let j := (r + 1) / 2
  let d := r / 2
  let H := H[S,q] (m + 1)
  let H' := H[S,q] (d + 1)
  let D := Hₗ[S,q] (d + 1)
  let L := S.chain
  let b := S.b
  let I := (J[S,q] j : Set G) * B[S] * (J[S,q] j : Set G)
  have hDepth := SimpleStratumLattice.simpleCriticalDepth_eq S.chain hcrit
  have hmf : (m : ℤ) < finiteCriticalDepth L S.n b := by
    rw [finiteCriticalDepth_of_criticalExponent_eq L S.n (r : ℤ) b hcrit]
    omega
  have hmcrit : ((m : ℤ) : WithTop ℤ) < simpleCriticalDepth S.chain S.b := by
    rw [hDepth, WithTop.coe_lt_coe]; omega
  have hseq := sequence_for_simple S hS0 hS q
  have hn : 0 < S.n := by have := S.r_lt_n; omega
  have hdet := (character_determinant_normalizer_finite L S.n ψF b q.tail m hmf hθ).1
  have hH : ∀ u : G, u ∈ H ↔ (u : A) - 1 ∈ Q L b (m + 1 : ℕ) ⊔ D := by
    intro u
    rw [simpleHGroup_mem_iff_of_pos S hS0 hS q (by omega)]
    obtain ⟨W, hW, hPW⟩ := hseq.exists_lattice_eq_relative_sup .H
    change simpleHLattice L S.n b q.tail = Q L b 0 ⊔ W at hW
    change W ≤ P L (simpleHCutoff (finiteCriticalDepth L S.n b)) at hPW
    rw [finiteCriticalDepth_of_criticalExponent_eq L S.n (r : ℤ) b hcrit,
      show simpleHCutoff (r : ℤ) = ((d + 1 : ℕ) : ℤ) by unfold simpleHCutoff d; omega] at hPW
    dsimp only [D, simpleHLayer]
    rw [hW]
    exact congrArg (fun M : Submodule O A => (u : A) - 1 ∈ M)
      (layer_eq_relative_sup_deep_of_le L b W (i := ((m + 1 : ℕ) : ℤ)) (by omega)
        (by dsimp [d]; omega) hPW) |>.to_iff
  have hH' (u : G) : u ∈ H' ↔ (u : A) - 1 ∈ D := simpleHGroup_mem_iff_of_pos S hS0 hS q (by omega)
  have hQD : Q L b (d + 1 : ℕ) ≤ D :=
    le_inf ((inf_le_inf_right _ (L.endFiltration_antitone (by omega))).trans
      (SimpleStratumLattice.centralizer_le_lattice L .H b q.tail)) inf_le_left
  have hmul : Q L b 0 * D ≤ D := by
    have hAdj := (hseq.properties hn .H).adjoint (r : ℤ) (by omega) hcrit.le (d + 1 : ℕ)
      (by change (r : ℤ) / 2 + 1 ≤ _; dsimp [d]; omega)
    exact (mul_le_mul_left (StratumEquivalence.centralizerLattice_le_adjointLattice L b (-(r : ℤ))) _).trans hAdj.1
  rw [simpleCharacterIntertwiningFactor_eq_cutoffJ_of_le S hS0 hS q hcrit
    (by omega : r / 2 < r) le_rfl] at hI
  rw [simpleCharacterIntertwiningFactor_eq_cutoffJ_of_le S hS0 hS q hcrit hmr hm.le]
  change characterSelfIntertwining θ = I
  let hinc : H' ≤ H := simpleHGroup_antitone _ _ _ _ (Nat.succ_le_succ hm.le)
  let χ := θ.comp (Subgroup.inclusion hinc)
  have hHigh : characterSelfIntertwining χ = I := hI
  have hBotCut : B[S] ⊆ characterSelfIntertwining χ := by
    rw [hHigh]
    intro g hg
    exact Set.mem_mul.mpr ⟨g, Set.mem_mul.mpr ⟨1, one_mem (J[S,q] j), g, hg, one_mul _⟩,
      1, one_mem (J[S,q] j), mul_one _⟩
  have hBot : B[S] ⊆ characterSelfIntertwining θ := fun _ hg =>
    centralizer_intertwines_of_deep_intertwining S hS.1 (by omega) (Nat.succ_le_succ hm.le)
      D H H' inf_le_right hQD hmul hH hH' hinc θ hdet hg (hBotCut hg)
  apply Set.Subset.antisymm
  · rw [← hHigh]
    exact characterSelfIntertwining_subset_of_agrees hinc θ χ (fun _ => rfl)
  · have hJ : J[S,q] j ≤ characterNormalizerSubgroup θ := fun _ hx =>
      simpleJ_le_characterNormalizerSubgroup ψF hψ S hS0 hS q m hmn hmcrit hθ
        (simpleJGroup_antitone _ _ _ _ (Nat.zero_le _) hx)
    exact sandwich_subset_characterSelfIntertwining θ hJ hBot

/-- The intertwining formula for every simple character, by induction on the
length of the chosen defining sequence and restriction to the cutoff. -/
theorem simpleCharacterSelfIntertwining
    (ψF : AddChar F ℂ) (hψ : IsBKAdditiveCharacter ψF)
    (S : Stratum O F V) (hS0 : S.r = 0) (hS : S.IsSimple) (q : S.DefiningSequenceChoice)
    (m : ℕ) (hmn : (m : ℤ) < S.n) (hmc : ((m : ℤ) : WithTop ℤ) < simpleCriticalDepth S.chain S.b)
    {θ : H[S,q] (m + 1) →* ℂˣ} (hθ : θ ∈ C[ψF,S,q] m) :
    characterSelfIntertwining θ = Y[S,q,m] * B[S] * Y[S,q,m] := by
  have bounded (d : ℕ) : ∀ (S : Stratum O F V), S.r = 0 → S.IsSimple → ∀ (q : S.DefiningSequenceChoice),
      q.steps < d → ∀ m : ℕ, (m : ℤ) < S.n → ((m : ℤ) : WithTop ℤ) < simpleCriticalDepth S.chain S.b →
      ∀ θ ∈ C[ψF,S,q] m, characterSelfIntertwining θ = Y[S,q,m] * B[S] * Y[S,q,m] := by
    induction d with
    | zero =>
      intro S hS0 hS q hq
      omega
    | succ d ih =>
      intro S hS0 hS q hq m hmn hmc θ hθ
      by_cases hb : elementAlgebra S.b = ⊥
      · exact (simpleCharacterIntertwining_of_scalar ψF S q hb m hθ).1
      · obtain ⟨r, hr, hrn, hcrit⟩ := criticalDepth_of_simple S hS0 hS q hb
        have hdepth := SimpleStratumLattice.simpleCriticalDepth_eq S.chain hcrit
        have hmr : m < r := by rw [hdepth, WithTop.coe_lt_coe] at hmc; exact_mod_cast hmc
        have high (i : ℕ) (hin : (i : ℤ) < S.n) (hir : i < r) (hi : r / 2 ≤ i)
            {χ : H[S,q] (i + 1) →* ℂˣ} (hχ : χ ∈ C[ψF,S,q] i) :=
          simpleCharacterIntertwining_high_of_successor ψF hψ S hS0 hS q
            (fun T hT0 hT q' hq' => ih T hT0 hT q' (by omega)) hr hin hir hi hcrit hχ
        rcases le_or_gt (r / 2) m with hm | hm
        · exact high m hmn hmr hm hθ
        · have hcutcrit : (((r / 2 : ℕ) : ℤ) : WithTop ℤ) < simpleCriticalDepth S.chain S.b := by
            rw [hdepth, WithTop.coe_lt_coe]; omega
          have hχ := simpleCharacters_restrict_forward ψF S hS0 hS q hm.le (by omega) hcutcrit hθ
          exact simpleCharacterIntertwining_low_of_cutoff ψF hψ S hS0 hS q hmn hmr hm hcrit hθ
            (high (r / 2) (by omega) (by omega) le_rfl hχ)
  exact bounded (q.steps + 1) S hS0 hS q (by omega) m hmn hmc θ hθ

end Langlands.BushnellKutzko
