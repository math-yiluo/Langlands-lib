import Langlands.BushnellKutzko.SimpleCharacterSuffixGroups
import Langlands.BushnellKutzko.SimpleCharacterTraceDual
import Langlands.BushnellKutzko.SimpleCharacterOuterGroup
import Langlands.BushnellKutzko.SimpleStratumLatticePropertiesProof
import Langlands.BushnellKutzko.SimpleIntertwiningProof
import Langlands.BushnellKutzko.LatticeCharacterIntertwining

/-! # Formal intertwining of the coset with error in the dual H lattice -/

noncomputable section

open ValuativeRel
open scoped Classical Pointwise

namespace Langlands.BushnellKutzko

universe uF uV

variable {F : Type uF} [Field F] [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F]
  {V : Type uV} [AddCommGroup V] [Module F V]

local notation "O" => 𝒪[F]
local notation "A" => Module.End F V
local notation "G" => (Module.End F V)ˣ
local notation "P" => LatticeChain.endFiltration
local notation "J[" S "," q "]" => simpleJGroup (Stratum.chain S) (Stratum.n S) (Stratum.b S)
  (Stratum.DefiningSequenceChoice.tail q)
local notation "H[" S "," q "]" => simpleHGroup (Stratum.chain S) (Stratum.n S) (Stratum.b S)
  (Stratum.DefiningSequenceChoice.tail q)
local notation "Jₗ[" S "," q "]" => simpleJLayer (Stratum.chain S) (Stratum.n S) (Stratum.b S)
  (Stratum.DefiningSequenceChoice.tail q)
local notation "Hₗ[" S "," q "]" => simpleHLayer (Stratum.chain S) (Stratum.n S) (Stratum.b S)
  (Stratum.DefiningSequenceChoice.tail q)

omit [TopologicalSpace F] [IsNonarchimedeanLocalField F] in
/-- Keeping the chain, level, and coefficient while changing the stratum depth. -/
def Stratum.atDepth (S : Stratum O F V) (m : ℤ) (hm : m < S.n) : Stratum O F V :=
  ⟨S.chain, S.n, m, S.b, hm, S.valuation_ge⟩

omit [TopologicalSpace F] [IsNonarchimedeanLocalField F] in
/-- Two coefficients with the same lattice coset give the same formal intertwining set. -/
theorem latticeCosetIntertwining_eq_of_sub_mem {b c : A} {D : Submodule O A} (h : b - c ∈ D) :
    latticeCosetIntertwining b D = latticeCosetIntertwining c D := by
  have he (x : A) : x - b ∈ D ↔ x - c ∈ D := by
    rw [show x - c = (x - b) + (b - c) by abel]
    exact ⟨fun hx => add_mem hx h, fun hx => (add_sub_cancel_right (x - b) (b - c)) ▸ sub_mem hx h⟩
  ext g
  change (∃ x : A, x - b ∈ D ∧ (↑g⁻¹ : A) * x * (g : A) - b ∈ D) ↔ _
  simp only [latticeCosetIntertwining, Set.mem_ofPred_eq, he]

omit [TopologicalSpace F] [IsNonarchimedeanLocalField F] in
/-- The outer subgroup is the join of the mixed adjoint congruence group
and the J group at the cutoff, with the finite critical depth supplied. -/
def simpleCharacterIntertwiningSubgroup (S : Stratum O F V) (q : S.DefiningSequenceChoice)
    (r m : ℕ) (hm : m < r) : Subgroup G :=
  mixedAdjointUnitGroup S.chain S.b (r - m) (-(r : ℤ)) (by omega) ⊔ J[S,q] ((r + 1) / 2)

/-- The weak lattice sequence associated with the chosen defining sequence. -/
theorem sequence_for_simple (S : Stratum O F V) (hS0 : S.r = 0) (hS : S.IsSimple)
    (q : S.DefiningSequenceChoice) : SimpleStratumLattice.Sequence S.chain S.n S.b q.tail :=
  SimpleStratumLattice.sequence_of_choice S.chain q rfl (by simpa [hS0] using hS.2)

omit [TopologicalSpace F] [IsNonarchimedeanLocalField F] in
private theorem nonscalar_of_criticalExponent_eq (S : Stratum O F V) {r : ℕ}
    (hr : criticalExponent S.chain S.b = ((-(r : ℤ) : ℤ) : WithBot ℤ)) : elementAlgebra S.b ≠ ⊥ := by
  intro h
  rw [criticalExponent, ite_eq_left h] at hr
  exact WithBot.bot_ne_coe hr

omit [TopologicalSpace F] [IsNonarchimedeanLocalField F] in
private theorem simpleJCutoff_toNat_of_critical (S : Stratum O F V) {r : ℕ}
    (hr : criticalExponent S.chain S.b = ((-(r : ℤ) : ℤ) : WithBot ℤ)) :
    (simpleJCutoff (finiteCriticalDepth S.chain S.n S.b)).toNat = (r + 1) / 2 := by
  rw [finiteCriticalDepth_of_criticalExponent_eq _ _ _ _ hr]
  unfold simpleJCutoff
  omega

private theorem fractional_eq_mixed (S : Stratum O F V) (hS : S.IsPure) {r m : ℕ} (hm : m < r) :
    centralizerLattice S.chain S.b ((r : ℤ) - m) * adjointLattice S.chain S.b (-(r : ℤ)) =
      mixedAdjointLattice S.chain S.b (r - m : ℕ) (-(r : ℤ)) := by
  have h := centralizerLattice_mul_mixedAdjointLattice S.chain S.b
    (SimpleStratumLattice.parameter_of_pure S.chain hS rfl).inverse ((r : ℤ) - m) 0 (-(r : ℤ))
  simpa only [mixedAdjointLattice_zero, add_zero, Nat.cast_sub hm.le] using h

/-- The deep J lattice is an adjoint bimodule at the critical exponent. -/
theorem simpleJLayer_cutoff_adjoint_bimodule (S : Stratum O F V) (hS0 : S.r = 0) (hS : S.IsSimple)
    (q : S.DefiningSequenceChoice) {r : ℕ}
    (hr : criticalExponent S.chain S.b = ((-(r : ℤ) : ℤ) : WithBot ℤ)) :
    SimpleStratumLattice.Bimodule (adjointLattice S.chain S.b (-(r : ℤ))) (Jₗ[S,q] ((r + 1) / 2)) :=
  ((sequence_for_simple S hS0 hS q).properties (by have := S.r_lt_n; omega) .J).adjoint
    (r : ℤ) (by omega) hr.le (((r + 1) / 2 : ℕ) : ℤ) (by change ((r : ℤ) + 1) / 2 ≤ _; omega)

/-- The subgroup product represents the fractional-lattice factor of the
character intertwining statement. -/
theorem coe_simpleCharacterIntertwiningSubgroup

    (S : Stratum O F V) (hS0 : S.r = 0) (hS : S.IsSimple) (q : S.DefiningSequenceChoice)
    {r m : ℕ} (hr : 0 < r) (hm : m < r)
    (hcrit : criticalExponent S.chain S.b = ((-(r : ℤ) : ℤ) : WithBot ℤ)) :
    (simpleCharacterIntertwiningSubgroup S q r m hm : Set G) = simpleCharacterIntertwiningFactor S q m := by
  have hK (g : G) : g ∈ J[S,q] ((r + 1) / 2) ↔ (g : A) - 1 ∈ Jₗ[S,q] ((r + 1) / 2) :=
    simpleJGroup_mem_iff_of_pos S hS0 hS q (by omega)
  have hN := simpleJLayer_cutoff_adjoint_bimodule S hS0 hS q hcrit
  unfold simpleCharacterIntertwiningFactor
  rw [ite_eq_right (nonscalar_of_criticalExponent_eq S hcrit)]
  dsimp only
  rw [simpleJCutoff_toNat_of_critical S hcrit,
    finiteCriticalDepth_of_criticalExponent_eq _ _ _ _ hcrit, fractional_eq_mixed S hS.1 hm]
  exact mixedAdjointUnitGroup_sup_eq_lattice S.chain S.b (show 1 ≤ r - m by omega) _ _ _ hK hN.1 hN.2

omit [TopologicalSpace F] [IsNonarchimedeanLocalField F] in
private theorem traceDualLattice_bimodule (ψF : AddChar F ℂ) {R M : Submodule O A}
    (hRM : R * M ≤ M) (hMR : M * R ≤ M) : SimpleStratumLattice.Bimodule R (traceDualLattice ψF M) := by
  constructor <;> apply Submodule.mul_le.mpr
  · intro x hx z hz y hy
    have ht := hz (y * x) (hMR (Submodule.mul_mem_mul hy hx))
    change traceCharacter ψF (x * z * y) = 1
    simpa only [traceCharacter_apply, ← mul_assoc z y x, LinearMap.trace_mul_cycle F z y x] using ht
  · intro z hz x hx y hy
    have ht := hz (x * y) (hRM (Submodule.mul_mem_mul hx hy))
    simpa only [← mul_assoc z x y] using ht

/-- At the J cutoff the adjoint image is contained in the dual H layer, and
that dual layer is stable under multiplication by the cutoff J layer. -/
theorem simpleCharacterTraceDual_bimodule (S : Stratum O F V) (hS0 : S.r = 0) (hS : S.IsSimple)
    (q : S.DefiningSequenceChoice) (ψF : AddChar F ℂ) (hψ : IsBKAdditiveCharacter ψF) {r m : ℕ}
    (hr : criticalExponent S.chain S.b = ((-(r : ℤ) : ℤ) : WithBot ℤ)) :
    let J := Jₗ[S,q] ((r + 1) / 2)
    let D := traceDualLattice ψF (Hₗ[S,q] (m + 1))
    J.map (adjointMap O S.b) ≤ D ∧ SimpleStratumLattice.Bimodule J D := by
  dsimp only
  have hI := (simpleStratumLatticeProperties F V S hS0 hS q).2.2.2.2.1.2.2 (m + 1) (by omega)
  have h := (sequence_for_simple S hS0 hS q).traceDual_simpleHLayer (by have := S.r_lt_n; omega) ψF hψ m
  rw [simpleJCutoff_toNat_of_critical S hr] at h
  refine ⟨h.symm ▸ le_sup_left, traceDualLattice_bimodule ψF ?_ ?_⟩
  · exact (mul_le_mul_left inf_le_left _).trans hI.2.1
  · exact (mul_le_mul_right inf_le_left _).trans hI.2.2

/-- For a unit satisfying the covariance identity on the character overlap,
character self-intertwining is equivalent to formal intertwining of the
parameter coset modulo the dual domain lattice. -/
theorem simpleCharacter_intertwining_iff_formal_of_ratio

    (S : Stratum O F V) (hS0 : S.r = 0) (hS : S.IsSimple) (q : S.DefiningSequenceChoice)
    (ψF : AddChar F ℂ) (hψ : IsBKAdditiveCharacter ψF) {m : ℕ} (θ : H[S,q] (m + 1) →* ℂˣ)
    {g : G} (hg : characterConjugationRatio ψF S.b θ g) :
    g ∈ characterSelfIntertwining θ ↔ g ∈ latticeCosetIntertwining S.b (traceDualLattice ψF (Hₗ[S,q] (m + 1))) := by
  let L := S.chain
  let M := Hₗ[S,q] (m + 1)
  let D := traceDualLattice ψF M
  let := L.finiteDimensional
  have hB := (sequence_for_simple S hS0 hS q).simpleHLayer_bounds (by have := S.r_lt_n; omega) (m + 1)
  have hFg : M.FG := (L.fg_endFiltration (m + 1 : ℕ)).of_le hB.2
  have hDFg : D.FG := by
    have h := traceDualLattice_antitone ψF hB.1
    rw [traceDualLattice_endFiltration L ψF hψ] at h
    exact (L.fg_endFiltration _).of_le h
  let e := (endUnitConjugation g⁻¹).toLinearMap
  have hDM : traceDualLattice ψF (M.map e) = D.map e := traceDualLattice_map_conj ψF g⁻¹ M
  have h := traceDualLattice_inf_aux ψF (traceDualLattice ψF) (fun _ _ => Iff.rfl)
    (mem_additiveDual_iff_trace ψF hψ) hFg (hFg.map e) hDFg (hDM.symm ▸ hDFg.map e)
  rw [hDM] at h
  exact mem_characterSelfIntertwining_iff_latticeCosetIntertwining L ψF S.b M D θ g
    (fun _ => simpleHGroup_mem_iff_of_pos S hS0 hS q (by omega))
    (hB.2.trans (L.endFiltration_antitone (by omega))) hg (congrArg SetLike.coe h)

private theorem formalIntertwining_neighborhood (S : Stratum O F V) (hS : S.IsPure)
    {r m : ℕ} (hmn : (m : ℤ) < S.n) (hmr : m < r)
    (hr : criticalExponent S.chain S.b = ((-(r : ℤ) : ℤ) : WithBot ℤ)) :
    (S.atDepth m hmn).simpleIntertwiningNeighborhood =
      (mixedAdjointUnitGroup S.chain S.b (r - m) (-(r : ℤ)) (by omega) : Set G) := by
  ext g
  constructor
  · rintro (⟨h, _⟩ | ⟨k, hk, h⟩)
    · exact (WithBot.coe_ne_bot (hr.symm.trans h)).elim
    · have hk' : k = -(r : ℤ) := WithBot.coe_injective (hk.symm.trans hr)
      subst k
      change (g : A) - 1 ∈ centralizerLattice S.chain S.b (-((m : ℤ) + -(r : ℤ))) *
        adjointLattice S.chain S.b (-(r : ℤ)) at h
      rw [show -((m : ℤ) + -(r : ℤ)) = (r : ℤ) - m by omega,
        fractional_eq_mixed S hS hmr] at h
      exact h
  · intro hg
    right
    refine ⟨-(r : ℤ), hr, ?_⟩
    change (g : A) - 1 ∈ centralizerLattice S.chain S.b (-((m : ℤ) + -(r : ℤ))) *
      adjointLattice S.chain S.b (-(r : ℤ))
    rw [show -((m : ℤ) + -(r : ℤ)) = (r : ℤ) - m by omega, fractional_eq_mixed S hS hmr]
    exact hg

/-- The ordinary coset at depth m has the mixed adjoint double coset as its
formal intertwining set, by BK93 (1.5.8). -/
theorem latticeCosetIntertwining_filtration_eq_mixed_doubleCoset (S : Stratum O F V) (hS : S.IsPure)
    {r m : ℕ} (hmn : (m : ℤ) < S.n) (hmr : m < r)
    (hr : criticalExponent S.chain S.b = ((-(r : ℤ) : ℤ) : WithBot ℤ)) :
    let X := mixedAdjointUnitGroup S.chain S.b (r - m) (-(r : ℤ)) (by omega)
    latticeCosetIntertwining S.b (P S.chain (-(m : ℤ))) = (X : Set G) * (centralizerUnitGroup S.b : Set G) * X := by
  let := S.chain.finiteDimensional
  let T := S.atDepth m hmn
  have hT : T.IsSimple := ⟨hS, hr.trans_lt (WithBot.coe_lt_coe.mpr (by omega : -(r : ℤ) < -(m : ℤ)))⟩
  have h := simpleIntertwining F V T hT
  change latticeCosetIntertwining S.b (P S.chain (-(m : ℤ))) =
    T.simpleIntertwiningNeighborhood * (centralizerUnitGroup S.b : Set G) * T.simpleIntertwiningNeighborhood at h
  rw [formalIntertwining_neighborhood S hS hmn hmr hr] at h
  exact h

/-- Conjugating the two representatives by cutoff J units reduces the
larger formal intertwining set to the ordinary stratum coset. -/
theorem simpleCharacter_formalIntertwining_eq_sandwich

    (S : Stratum O F V) (hS0 : S.r = 0) (hS : S.IsSimple) (q : S.DefiningSequenceChoice)
    (ψF : AddChar F ℂ) (hψ : IsBKAdditiveCharacter ψF) {r m : ℕ} (hr : 0 < r)
    (hcrit : criticalExponent S.chain S.b = ((-(r : ℤ) : ℤ) : WithBot ℤ)) :
    let K := J[S,q] ((r + 1) / 2)
    latticeCosetIntertwining S.b (traceDualLattice ψF (Hₗ[S,q] (m + 1))) =
      (K : Set G) * latticeCosetIntertwining S.b (P S.chain (-(m : ℤ))) * (K : Set G) := by
  let L := S.chain
  let b := S.b
  let j := (r + 1) / 2
  let J := Jₗ[S,q] j
  let K := J[S,q] j
  let D := traceDualLattice ψF (Hₗ[S,q] (m + 1))
  have hK (x : G) : x ∈ K ↔ (x : A) - 1 ∈ J := simpleJGroup_mem_iff_of_pos S hS0 hS q (by dsimp [j]; omega)
  have hD : D = J.map (adjointMap O b) ⊔ P L (-(m : ℤ)) := by
    have h := (sequence_for_simple S hS0 hS q).traceDual_simpleHLayer (by have := S.r_lt_n; omega) ψF hψ m
    rwa [simpleJCutoff_toNat_of_critical S hcrit] at h
  have hJpos : J ≤ P L 1 := inf_le_right.trans (L.endFiltration_antitone (by dsimp [j]; omega))
  obtain ⟨hA, hJD, hDJ⟩ := simpleCharacterTraceDual_bimodule S hS0 hS q ψF hψ (m := m) hcrit
  have hpres (g : G) (hg : g ∈ K) (x : A) (hx : x - b ∈ D) : (↑g⁻¹ : A) * x * (g : A) - b ∈ D :=
    latticeCoset_conj_sub_mem_of_adjoint_image b hJD hDJ hA ((hK _).mp hg) ((hK _).mp (K.inv_mem hg)) hx
  have hmove (x : A) (hx : x - b ∈ D) : ∃ g ∈ K, (↑g⁻¹ : A) * x * (g : A) - b ∈ P L (-(m : ℤ)) := by
    have hlevels : ∃ k : ℤ, x - b ∈ P L k := by
      by_cases hz : x - b = 0
      · exact ⟨0, hz ▸ zero_mem _⟩
      · exact (radicalFiltration F V L).2.2.2.2 _ hz |>.1
    obtain ⟨k, hk⟩ := hlevels
    simpa only [add_sub_cancel] using
      exists_conj_sub_mem_filtration_of_adjoint_image L b D J K (-(m : ℤ)) hK hJpos hJD hDJ hD hx hk
  have hsub : P L (-(m : ℤ)) ≤ D := hD.symm ▸ le_sup_right
  exact latticeCosetIntertwining_eq_sandwich b K hsub hpres hmove

/-- The formal intertwining set of the larger dual-lattice coset is the
outer-group double coset of the centralizer. The depth-raising correction
reduces the larger coset to the ordinary stratum coset. -/
theorem simpleCharacter_formalIntertwining_eq_doubleCoset

    (S : Stratum O F V) (hS0 : S.r = 0) (hS : S.IsSimple) (q : S.DefiningSequenceChoice)
    (ψF : AddChar F ℂ) (hψ : IsBKAdditiveCharacter ψF) {r m : ℕ} (hr : 0 < r)
    (hmn : (m : ℤ) < S.n) (hmr : m < r)
    (hcrit : criticalExponent S.chain S.b = ((-(r : ℤ) : ℤ) : WithBot ℤ)) :
    let Y := simpleCharacterIntertwiningFactor S q m
    latticeCosetIntertwining S.b (traceDualLattice ψF (Hₗ[S,q] (m + 1))) =
      Y * (centralizerUnitGroup S.b : Set G) * Y := by
  let L := S.chain
  let b := S.b
  let j := (r + 1) / 2
  let J := Jₗ[S,q] j
  let K := J[S,q] j
  let X := mixedAdjointUnitGroup L b (r - m) (-(r : ℤ)) (by omega)
  let Y := simpleCharacterIntertwiningSubgroup S q r m hmr
  have hK (x : G) : x ∈ K ↔ (x : A) - 1 ∈ J := simpleJGroup_mem_iff_of_pos S hS0 hS q (by dsimp [j]; omega)
  have hNorm := simpleJLayer_cutoff_adjoint_bimodule S hS0 hS q hcrit
  have hX : X ≤ Subgroup.normalizer (K : Set G) :=
    mixedAdjointUnitGroup_le_normalizer_of_adjoint_bimodule L b (by omega) _ J K hK hNorm.1 hNorm.2
  have hYl : (Y : Set G) = (K : Set G) * (X : Set G) := by
    change (↑(X ⊔ K) : Set G) = _
    rw [sup_comm]
    exact Subgroup.coe_mul_of_right_le_normalizer_left K X hX
  have hYr : (Y : Set G) = (X : Set G) * (K : Set G) := Subgroup.coe_mul_of_left_le_normalizer_right X K hX
  have hY := coe_simpleCharacterIntertwiningSubgroup S hS0 hS q hr hmr hcrit
  dsimp only
  rw [← hY]
  change latticeCosetIntertwining b (traceDualLattice ψF (Hₗ[S,q] (m + 1))) = (Y : Set G) * (centralizerUnitGroup b : Set G) * (Y : Set G)
  rw [simpleCharacter_formalIntertwining_eq_sandwich S hS0 hS q ψF hψ hr hcrit,
    latticeCosetIntertwining_filtration_eq_mixed_doubleCoset S hS.1 hmn hmr hcrit]
  change (K : Set G) * ((X : Set G) * (centralizerUnitGroup b : Set G) * X) * K = _
  calc
    _ = ((K : Set G) * X) * (centralizerUnitGroup b : Set G) * ((X : Set G) * K) := by simp only [mul_assoc]
    _ = _ := by rw [← hYl, ← hYr]

end Langlands.BushnellKutzko
