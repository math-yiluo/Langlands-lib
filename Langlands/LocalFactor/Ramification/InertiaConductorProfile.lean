import Langlands.LocalFactor.Ramification.Breaks
import Langlands.LocalFactor.Ramification.InertiaPresentationStatement
import Langlands.LocalFactor.Ramification.Herbrand.WeilBreakProof
import Langlands.Representation.Smooth.FixedVectors.OrderProof
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic

/-!
# Upper fixed-space profiles of inertia Artin and Swan conductors

The Swan expression of a representation of an actual finite inertia group is the
integral over `[0, B]` of the codimension of the upper-group fixed vectors, for every
`B` beyond the last Herbrand break. The Artin expression adds the codimension at `0`.
Two actual finite inertia representations on the same vector space have equal
conductors whenever their upper fixed-space dimensions agree. The application to
refinement is exported by `InertiaConductorRefinementProof`.
-/

noncomputable section

namespace Langlands.Ramification.Padic

open Module MeasureTheory Set
open scoped BigOperators

universe uK uL uL' uV

section Profile

variable {p : ℕ} [Fact p.Prime] {F : PadicField.{uL} p}
  (T : F.TopologicalData) (K : Type uK) [Field K] [Algebra (Padic p) K]
  [Algebra K F.Carrier] [IsScalarTower (Padic p) K F.Carrier]
  {V : Type uV} [AddCommGroup V] [Module ℂ V] [FiniteDimensional ℂ V]
  (ρ : Representation ℂ (inertia T K) V)

/-- The codimension of the fixed vectors of the actual upper group `G^v`, as a real
function of `v`. -/
def upperCodimensionProfile (v : ℝ) : ℝ :=
  (finrank ℂ V : ℝ) - (finrank ℂ (inertiaUpperFixedVectors T K ρ v) : ℝ)

omit [FiniteDimensional ℂ V] in
theorem inertiaUpperFixedVectors_monotone :
    Monotone (inertiaUpperFixedVectors T K ρ) := by
  intro v w hvw
  apply fixedVectors_antitone
  intro x hx
  exact Subgroup.mem_subgroupOf.mpr
    (upperRamificationGroup_antitone T K hvw (Subgroup.mem_subgroupOf.mp hx))

theorem upperCodimensionProfile_antitone : Antitone (upperCodimensionProfile T K ρ) := by
  intro v w hvw
  unfold upperCodimensionProfile
  have := Submodule.finrank_mono (inertiaUpperFixedVectors_monotone T K ρ hvw)
  have h' : ((finrank ℂ (inertiaUpperFixedVectors T K ρ v) : ℕ) : ℝ) ≤
      (finrank ℂ (inertiaUpperFixedVectors T K ρ w) : ℝ) := by exact_mod_cast this
  linarith

theorem upperCodimensionProfile_intervalIntegrable (a b : ℝ) :
    IntervalIntegrable (upperCodimensionProfile T K ρ) volume a b :=
  (upperCodimensionProfile_antitone T K ρ).intervalIntegrable

/-- Herbrand's function at a natural number is the normalized partial sum of the
orders of the higher lower groups. -/
theorem herbrandPhi_natCast (i : ℕ) :
    herbrandPhi T K i =
      (∑ k ∈ Finset.range i, (lowerGroupOrder T K (k + 1) : ℝ)) / lowerGroupOrder T K 0 := by
  rw [herbrandPhi_floor T K (Nat.cast_nonneg i), Nat.floor_natCast, sub_self, zero_mul,
    add_zero]

theorem herbrandPhi_succ_sub (i : ℕ) :
    herbrandPhi T K ((i + 1 : ℕ) : ℝ) - herbrandPhi T K (i : ℝ) =
      (lowerGroupOrder T K (i + 1) : ℝ) / lowerGroupOrder T K 0 := by
  rw [herbrandPhi_natCast, herbrandPhi_natCast, Finset.sum_range_succ, ← sub_div]
  ring_nf

theorem herbrandPhi_natCast_nonneg (i : ℕ) : 0 ≤ herbrandPhi T K (i : ℝ) := by
  have := (herbrandPhi_strictMono T K).monotone (Nat.cast_nonneg (α := ℝ) i)
  simpa using this

omit [FiniteDimensional ℂ V] in
/-- Between consecutive integral Herbrand values the upper fixed space is the fixed
space of the next lower group. -/
theorem inertiaUpperFixedVectors_of_mem_Ioc (i : ℕ) {v : ℝ}
    (hv : v ∈ Ioc (herbrandPhi T K (i : ℝ)) (herbrandPhi T K ((i + 1 : ℕ) : ℝ))) :
    inertiaUpperFixedVectors T K ρ v = fixedVectors ρ (inertiaLowerGroup T K (i + 1)) := by
  have hv0 : 0 ≤ v := (herbrandPhi_natCast_nonneg T K i).trans hv.1.le
  rw [inertiaUpperFixedVectors_eq_natceil T K ρ hv0]
  congr 2
  rw [Nat.ceil_eq_iff (Nat.succ_ne_zero i)]
  have h1 := herbrandPsi_strictMono T K hv.1
  have h2 := (herbrandPsi_strictMono T K).monotone hv.2
  rw [herbrandPsi_herbrandPhi] at h1 h2
  simpa using And.intro h1 h2

/-- The cardinality of a lower group regarded inside inertia. -/
theorem card_inertiaLowerGroup (i : ℕ) :
    Nat.card (inertiaLowerGroup T K i) = lowerGroupOrder T K i := by
  have hle : lowerRamificationGroup T K i ≤ inertia T K := by
    rw [← lowerRamificationGroup_zero]
    exact lowerRamificationGroup_antitone T K (Nat.zero_le i)
  exact Nat.card_congr (Subgroup.subgroupOfEquivOfLe hle).toEquiv

theorem inertiaLowerGroup_eq_bot_of_cutoff (i : ℕ) (hi : ramificationCutoff T K ≤ i) :
    inertiaLowerGroup T K i = ⊥ := by
  rw [inertiaLowerGroup, lowerRamificationGroup_eq_bot_of_cutoff T K i hi,
    Subgroup.bot_subgroupOf]

/-- The rational Swan expression as a finite sum over the lower indices below the
cutoff, with the weights `g_(i+1)/g_0` and the fixed-space codimensions. -/
theorem inertiaSwanConductor_eq_sum_rat :
    inertiaSwanConductor T K ρ =
      ∑ i ∈ Finset.range (ramificationCutoff T K),
        (lowerGroupOrder T K (i + 1) : ℚ) / lowerGroupOrder T K 0 *
          ((finrank ℂ V : ℚ) -
            finrank ℂ (fixedVectors ρ (inertiaLowerGroup T K (i + 1)))) := by
  let := inertiaIntegerAction T K
  have : FaithfulSMul (inertia T K) T.Integers := by
    let := integerAction T K
    have hfaithG : FaithfulSMul (F.Carrier ≃ₐ[K] F.Carrier) T.Integers := by
      let := T.valuativeRel
      have : IsFractionRing T.Integers F.Carrier :=
        inferInstanceAs (IsFractionRing
          (ValuativeRel.valuation F.Carrier).valuationSubring F.Carrier)
      refine ⟨fun {σ τ} h => ?_⟩
      have heq : σ.toRingHom = τ.toRingHom :=
        IsFractionRing.ringHom_ext (A := T.Integers) (fun x =>
          congrArg (fun y : T.Integers => (y : F.Carrier)) (h x))
      exact AlgEquiv.ext fun x => RingHom.congr_fun heq x
    exact ⟨fun {σ τ} h => Subtype.ext (FaithfulSMul.eq_of_smul_eq_smul (α := T.Integers) h)⟩
  have : IsNoetherianRing T.Integers := by
    let := T.topology
    let := T.valuativeRel
    let := T.localField
    infer_instance
  have : Finite (F.Carrier ≃ₐ[K] F.Carrier) := by
    have : FiniteDimensional K F.Carrier :=
      Module.Finite.of_restrictScalars_finite (Padic p) K F.Carrier
    infer_instance
  change Ramification.swanConductor T.Integers (inertia T K) ρ = _
  rw [Ramification.swanConductor_eq_sum_range T.Integers (inertia T K) ρ
    (ramificationCutoff T K) (fun i hi => inertiaLowerGroup_eq_bot_of_cutoff T K i hi)]
  apply Finset.sum_congr rfl
  intro i _
  show (Nat.card (inertiaLowerGroup T K (i + 1)) : ℚ) / Nat.card (inertiaLowerGroup T K 0) *
      ((finrank ℂ V - finrank ℂ (fixedVectors ρ (inertiaLowerGroup T K (i + 1))) : ℕ) : ℚ) = _
  rw [card_inertiaLowerGroup, card_inertiaLowerGroup, Nat.cast_sub (Submodule.finrank_le _)]

/-- The real Swan expression as the same finite sum. -/
theorem inertiaSwanConductor_eq_sum :
    (inertiaSwanConductor T K ρ : ℝ) =
      ∑ i ∈ Finset.range (ramificationCutoff T K),
        (lowerGroupOrder T K (i + 1) : ℝ) / lowerGroupOrder T K 0 *
          ((finrank ℂ V : ℝ) -
            finrank ℂ (fixedVectors ρ (inertiaLowerGroup T K (i + 1)))) := by
  rw [inertiaSwanConductor_eq_sum_rat]
  push_cast
  rfl

omit [FiniteDimensional ℂ V] in
/-- Each lower piece of the Swan sum is the integral of the codimension profile over
the corresponding Herbrand interval. -/
theorem integral_upperCodimensionProfile_piece (i : ℕ) :
    ∫ v in herbrandPhi T K (i : ℝ)..herbrandPhi T K ((i + 1 : ℕ) : ℝ),
        upperCodimensionProfile T K ρ v =
      (lowerGroupOrder T K (i + 1) : ℝ) / lowerGroupOrder T K 0 *
        ((finrank ℂ V : ℝ) - finrank ℂ (fixedVectors ρ (inertiaLowerGroup T K (i + 1)))) := by
  have hle : herbrandPhi T K (i : ℝ) ≤ herbrandPhi T K ((i + 1 : ℕ) : ℝ) :=
    (herbrandPhi_strictMono T K).monotone (by push_cast; linarith)
  rw [intervalIntegral.integral_congr_Ioo_of_le hle
    (g := fun _ => (finrank ℂ V : ℝ) -
      finrank ℂ (fixedVectors ρ (inertiaLowerGroup T K (i + 1)))),
    intervalIntegral.integral_const, herbrandPhi_succ_sub, smul_eq_mul]
  intro v hv
  simp only [upperCodimensionProfile]
  rw [inertiaUpperFixedVectors_of_mem_Ioc T K ρ i (Ioo_subset_Ioc_self hv)]

omit [FiniteDimensional ℂ V] in
/-- Beyond the last Herbrand break the codimension profile vanishes. -/
theorem upperCodimensionProfile_eq_zero {v : ℝ}
    (hv : herbrandPhi T K (ramificationCutoff T K : ℝ) < v) :
    upperCodimensionProfile T K ρ v = 0 := by
  have hv0 : 0 ≤ v := (herbrandPhi_natCast_nonneg T K _).trans hv.le
  have hpsi := herbrandPsi_strictMono T K hv
  rw [herbrandPsi_herbrandPhi] at hpsi
  have hceil : ramificationCutoff T K ≤ ⌈herbrandPsi T K v⌉₊ :=
    Nat.cast_le.mp ((le_of_lt hpsi).trans (Nat.le_ceil _))
  unfold upperCodimensionProfile
  rw [inertiaUpperFixedVectors_eq_natceil T K ρ hv0,
    inertiaFixedVectors_eq_top_of_lower_eq_bot T K ρ
      (lowerRamificationGroup_eq_bot_of_cutoff T K _ hceil), finrank_top, sub_self]

/-- **Profile formula.** The real Swan expression is the integral of the upper
codimension profile over `[0, B]`, for every `B` beyond the last Herbrand break. -/
theorem inertiaSwanConductor_eq_integral (B : ℝ)
    (hB : herbrandPhi T K (ramificationCutoff T K : ℝ) ≤ B) :
    (inertiaSwanConductor T K ρ : ℝ) =
      ∫ v in (0 : ℝ)..B, upperCodimensionProfile T K ρ v := by
  set N := ramificationCutoff T K
  have hsum : ∑ i ∈ Finset.range N,
      ∫ v in herbrandPhi T K (i : ℝ)..herbrandPhi T K ((i + 1 : ℕ) : ℝ),
        upperCodimensionProfile T K ρ v =
      ∫ v in herbrandPhi T K ((0 : ℕ) : ℝ)..herbrandPhi T K (N : ℝ),
        upperCodimensionProfile T K ρ v :=
    intervalIntegral.sum_integral_adjacent_intervals (a := fun i : ℕ => herbrandPhi T K i)
      (fun k _ => upperCodimensionProfile_intervalIntegrable T K ρ _ _)
  simp only [Nat.cast_zero, herbrandPhi_zero] at hsum
  have htail : ∫ v in herbrandPhi T K (N : ℝ)..B, upperCodimensionProfile T K ρ v = 0 := by
    rw [intervalIntegral.integral_congr_Ioo_of_le hB (g := fun _ => (0 : ℝ)),
      intervalIntegral.integral_zero]
    intro v hv
    exact upperCodimensionProfile_eq_zero T K ρ hv.1
  rw [← intervalIntegral.integral_add_adjacent_intervals
    (upperCodimensionProfile_intervalIntegrable T K ρ 0 (herbrandPhi T K (N : ℝ)))
    (upperCodimensionProfile_intervalIntegrable T K ρ _ B), htail, add_zero, ← hsum,
    inertiaSwanConductor_eq_sum]
  apply Finset.sum_congr rfl
  intro i _
  rw [integral_upperCodimensionProfile_piece]

/-- The tame term is the codimension at the upper index `0`. -/
theorem fixedCodimension_top_eq_profile_zero :
    ((Ramification.fixedCodimension (inertia T K) ρ ⊤ : ℚ) : ℝ) =
      upperCodimensionProfile T K ρ 0 := by
  have h0 : inertiaUpperFixedVectors T K ρ 0 = fixedVectors ρ ⊤ := by
    rw [inertiaUpperFixedVectors, upperRamificationGroup_zero, Subgroup.subgroupOf_self]
  unfold upperCodimensionProfile Ramification.fixedCodimension
  rw [h0, Nat.cast_sub (Submodule.finrank_le _)]
  push_cast
  ring

/-- The real Artin expression is the codimension at `0` plus the profile integral. -/
theorem inertiaArtinConductor_eq_integral (B : ℝ)
    (hB : herbrandPhi T K (ramificationCutoff T K : ℝ) ≤ B) :
    (inertiaArtinConductor T K ρ : ℝ) =
      upperCodimensionProfile T K ρ 0 +
        ∫ v in (0 : ℝ)..B, upperCodimensionProfile T K ρ v := by
  rw [inertiaArtinConductor_eq_tame_add_swan, Rat.cast_add,
    fixedCodimension_top_eq_profile_zero, inertiaSwanConductor_eq_integral T K ρ B hB]

end Profile

section Refinement

open Weil.Local

variable {p : ℕ} [Fact p.Prime]

/-- Two representations of actual finite inertia groups with the same upper fixed-space
dimensions at every nonnegative index have the same Artin and Swan expressions. -/
theorem inertiaConductors_eq_of_upperFixedDimension
    {F : PadicField.{uL} p} {F' : PadicField.{uL'} p}
    (T : F.TopologicalData) (T' : F'.TopologicalData)
    (K : Type uK) [Field K] [Algebra (Padic p) K]
    [Algebra K F.Carrier] [IsScalarTower (Padic p) K F.Carrier]
    [Algebra K F'.Carrier] [IsScalarTower (Padic p) K F'.Carrier]
    {V : Type uV} [AddCommGroup V] [Module ℂ V] [FiniteDimensional ℂ V]
    (ρ : Representation ℂ (inertia T K) V) (ρ' : Representation ℂ (inertia T' K) V)
    (h : ∀ v : ℝ, 0 ≤ v →
      finrank ℂ (inertiaUpperFixedVectors T K ρ v) =
        finrank ℂ (inertiaUpperFixedVectors T' K ρ' v)) :
    inertiaArtinConductor T' K ρ' = inertiaArtinConductor T K ρ ∧
    inertiaSwanConductor T' K ρ' = inertiaSwanConductor T K ρ := by
  set B := max (herbrandPhi T K (ramificationCutoff T K : ℝ))
    (herbrandPhi T' K (ramificationCutoff T' K : ℝ))
  have hB0 : 0 ≤ B := (herbrandPhi_natCast_nonneg T K _).trans (le_max_left _ _)
  have hprof : ∀ v : ℝ, 0 ≤ v →
      upperCodimensionProfile T' K ρ' v = upperCodimensionProfile T K ρ v := by
    intro v hv
    simp only [upperCodimensionProfile, h v hv]
  have hint : ∫ v in (0 : ℝ)..B, upperCodimensionProfile T' K ρ' v =
      ∫ v in (0 : ℝ)..B, upperCodimensionProfile T K ρ v := by
    apply intervalIntegral.integral_congr
    intro v hv
    rw [uIcc_of_le hB0] at hv
    exact hprof v hv.1
  have hswan : (inertiaSwanConductor T' K ρ' : ℝ) = inertiaSwanConductor T K ρ := by
    rw [inertiaSwanConductor_eq_integral T K ρ B (le_max_left _ _),
      inertiaSwanConductor_eq_integral T' K ρ' B (le_max_right _ _), hint]
  have hartin : (inertiaArtinConductor T' K ρ' : ℝ) = inertiaArtinConductor T K ρ := by
    rw [inertiaArtinConductor_eq_integral T K ρ B (le_max_left _ _),
      inertiaArtinConductor_eq_integral T' K ρ' B (le_max_right _ _), hint,
      hprof 0 le_rfl]
  exact ⟨Rat.cast_injective hartin, Rat.cast_injective hswan⟩

end Refinement

end Langlands.Ramification.Padic
