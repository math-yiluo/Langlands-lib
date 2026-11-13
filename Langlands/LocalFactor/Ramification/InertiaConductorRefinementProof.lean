import Langlands.LocalFactor.Ramification.InertiaPresentationStatement
import Langlands.LocalFactor.Ramification.Herbrand.WeilBreakProof
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic

/-!
# Refining an inertia presentation preserves its Artin and Swan sums

For a complex representation `ρ` of the actual finite inertia group of a finite
extension, the Swan sum is the integral over `[0, B]` of the codimension of the
upper-group fixed space, for any `B` beyond the image under Herbrand's `φ` of the
ramification cutoff. The Artin sum adds the codimension at `0`. Two finite inertia
presentations of the same Weil representation have the same upper fixed spaces at
every nonnegative index, so they have the same sums.
-/

noncomputable section

namespace Langlands.Ramification.Padic

open Module MeasureTheory Weil.Local
open scoped BigOperators

namespace InertiaConductorRefinement

universe uK uL uV

variable {p : ℕ} [Fact p.Prime] {F : PadicField.{uL} p}
  (T : F.TopologicalData) (K : Type uK) [Field K] [Algebra (Padic p) K]
  [Algebra K F.Carrier] [IsScalarTower (Padic p) K F.Carrier]

private theorem integers_isNoetherianRing : IsNoetherianRing T.Integers := by
  let := T.topology
  let := T.valuativeRel
  let := T.localField
  infer_instance

private theorem automorphisms_finite : Finite (F.Carrier ≃ₐ[K] F.Carrier) := by
  have : FiniteDimensional K F.Carrier :=
    Module.Finite.of_restrictScalars_finite (Padic p) K F.Carrier
  infer_instance

private theorem inertiaAction_faithful :
    letI := inertiaIntegerAction T K
    FaithfulSMul (inertia T K) T.Integers := by
  let := inertiaIntegerAction T K
  let := T.valuativeRel
  have : IsFractionRing T.Integers F.Carrier :=
    inferInstanceAs (IsFractionRing
      (ValuativeRel.valuation F.Carrier).valuationSubring F.Carrier)
  refine ⟨fun {σ τ} h => Subtype.ext ?_⟩
  have heq : (σ : F.Carrier ≃ₐ[K] F.Carrier).toRingHom =
      (τ : F.Carrier ≃ₐ[K] F.Carrier).toRingHom :=
    IsFractionRing.ringHom_ext (A := T.Integers) (fun x =>
      congrArg (fun y : T.Integers => (y : F.Carrier)) (h x))
  exact AlgEquiv.ext fun x => RingHom.congr_fun heq x

/-- The lower group `G_i`, regarded inside inertia, has `lowerGroupOrder` elements. -/
theorem card_inertiaLowerGroup (i : ℕ) :
    Nat.card (inertiaLowerGroup T K i) = lowerGroupOrder T K i := by
  have hle : lowerRamificationGroup T K i ≤ inertia T K := by
    rw [← lowerRamificationGroup_zero T K]
    exact lowerRamificationGroup_antitone T K (Nat.zero_le i)
  exact Nat.card_congr (Subgroup.subgroupOfEquivOfLe hle).toEquiv

/-- Herbrand's `φ` has slope `g_(i+1) / g_0` on `[i, i + 1]`. -/
theorem herbrandPhi_succ_sub (i : ℕ) :
    herbrandPhi T K ((i : ℝ) + 1) - herbrandPhi T K i =
      (lowerGroupOrder T K (i + 1) : ℝ) / lowerGroupOrder T K 0 := by
  have h1 := herbrandPhi_floor T K (u := ((i + 1 : ℕ) : ℝ)) (Nat.cast_nonneg _)
  have h0 := herbrandPhi_floor T K (u := (i : ℝ)) (Nat.cast_nonneg _)
  rw [Nat.floor_natCast] at h1 h0
  simp only [sub_self, zero_mul, add_zero] at h1 h0
  push_cast at h1
  rw [h1, h0, Finset.sum_range_succ]
  have hg : (lowerGroupOrder T K 0 : ℝ) ≠ 0 := by
    exact_mod_cast (lowerGroupOrder_pos T K 0).ne'
  field_simp
  ring

variable {V : Type uV} [AddCommGroup V] [Module ℂ V] [FiniteDimensional ℂ V]
  (ρ : Representation ℂ (inertia T K) V)

omit [FiniteDimensional ℂ V] in
/-- Upper fixed spaces grow with the upper index. -/
theorem inertiaUpperFixedVectors_monotone :
    Monotone (inertiaUpperFixedVectors T K ρ) := by
  intro r s hrs v hv g
  exact hv ⟨g, Subgroup.mem_subgroupOf.mpr
    (upperRamificationGroup_antitone T K hrs (Subgroup.mem_subgroupOf.mp g.property))⟩

omit [FiniteDimensional ℂ V] in
/-- Strictly between `φ(i)` and `φ(i + 1)`, the upper fixed space is the `G_(i+1)`-fixed
space. -/
theorem inertiaUpperFixedVectors_of_mem_Ioo (i : ℕ) {v : ℝ}
    (hv : v ∈ Set.Ioo (herbrandPhi T K i) (herbrandPhi T K ((i : ℝ) + 1))) :
    inertiaUpperFixedVectors T K ρ v = fixedVectors ρ (inertiaLowerGroup T K (i + 1)) := by
  have hi : 0 ≤ herbrandPhi T K i := by
    have := (herbrandPhi_strictMono T K).monotone (Nat.cast_nonneg i : (0 : ℝ) ≤ i)
    rwa [herbrandPhi_zero] at this
  have h1 := herbrandPsi_strictMono T K hv.1
  have h2 := herbrandPsi_strictMono T K hv.2
  rw [herbrandPsi_herbrandPhi] at h1 h2
  have hc : ⌈herbrandPsi T K v⌉₊ = i + 1 := by
    rw [Nat.ceil_eq_iff (Nat.succ_ne_zero i)]
    constructor
    · simpa using h1
    · exact_mod_cast h2.le
  rw [inertiaUpperFixedVectors_eq_natceil T K ρ (hi.trans hv.1.le), hc]

omit [FiniteDimensional ℂ V] in
/-- At and beyond `φ` of the ramification cutoff, every vector is fixed. -/
theorem inertiaUpperFixedVectors_eq_top {v : ℝ}
    (hv : herbrandPhi T K (ramificationCutoff T K) ≤ v) :
    inertiaUpperFixedVectors T K ρ v = ⊤ := by
  have hpsi := (herbrandPsi_strictMono T K).monotone hv
  rw [herbrandPsi_herbrandPhi] at hpsi
  have hbot : upperRamificationGroup T K v = ⊥ :=
    lowerRamificationGroupReal_eq_bot_of_cutoff T K hpsi
  rw [eq_top_iff]
  intro x _ g
  have hg : (g : inertia T K) = 1 := by
    apply Subtype.ext
    exact Subgroup.mem_bot.mp (hbot.le (Subgroup.mem_subgroupOf.mp g.property))
  change ρ (g : inertia T K) x = x
  rw [hg, map_one, Module.End.one_apply]

omit [FiniteDimensional ℂ V] in
/-- The upper fixed space at `0` is the space of inertia invariants. -/
theorem inertiaUpperFixedVectors_zero :
    inertiaUpperFixedVectors T K ρ 0 = fixedVectors ρ ⊤ := by
  simpa using inertiaUpperFixedVectors_phi T K ρ 0

/-- The codimension of the upper fixed space, as a real function of the upper index. -/
def upperCodimension (v : ℝ) : ℝ :=
  (finrank ℂ V : ℝ) - finrank ℂ (inertiaUpperFixedVectors T K ρ v)

theorem upperCodimension_antitone : Antitone (upperCodimension T K ρ) := by
  intro r s hrs
  have h := Submodule.finrank_mono (inertiaUpperFixedVectors_monotone T K ρ hrs)
  have h' : (finrank ℂ (inertiaUpperFixedVectors T K ρ r) : ℝ) ≤
      finrank ℂ (inertiaUpperFixedVectors T K ρ s) := by
    exact_mod_cast h
  simp only [upperCodimension]
  linarith

theorem upperCodimension_intervalIntegrable (a c : ℝ) :
    IntervalIntegrable (upperCodimension T K ρ) volume a c :=
  (upperCodimension_antitone T K ρ).intervalIntegrable

omit [FiniteDimensional ℂ V] in
/-- The integral over one lower step is the corresponding Swan summand. -/
theorem integral_upperCodimension_step (i : ℕ) :
    ∫ v in herbrandPhi T K i..herbrandPhi T K ((i : ℝ) + 1), upperCodimension T K ρ v =
      (lowerGroupOrder T K (i + 1) : ℝ) / lowerGroupOrder T K 0 *
        ((finrank ℂ V : ℝ) - finrank ℂ (fixedVectors ρ (inertiaLowerGroup T K (i + 1)))) := by
  have hle : herbrandPhi T K i ≤ herbrandPhi T K ((i : ℝ) + 1) :=
    (herbrandPhi_strictMono T K).monotone (by linarith)
  rw [intervalIntegral.integral_congr_Ioo_of_le hle
    (g := fun _ => (finrank ℂ V : ℝ) -
      finrank ℂ (fixedVectors ρ (inertiaLowerGroup T K (i + 1)))) ?_]
  · rw [intervalIntegral.integral_const, smul_eq_mul, herbrandPhi_succ_sub]
  · intro v hv
    rw [upperCodimension, inertiaUpperFixedVectors_of_mem_Ioo T K ρ i hv]

/-- The Swan sum is a finite sum over the lower steps below the cutoff. -/
theorem inertiaSwanConductor_eq_sum :
    (inertiaSwanConductor T K ρ : ℝ) =
      ∑ i ∈ Finset.range (ramificationCutoff T K),
        (lowerGroupOrder T K (i + 1) : ℝ) / lowerGroupOrder T K 0 *
          ((finrank ℂ V : ℝ) - finrank ℂ (fixedVectors ρ (inertiaLowerGroup T K (i + 1)))) := by
  let := inertiaIntegerAction T K
  have := inertiaAction_faithful T K
  have := integers_isNoetherianRing T
  have := automorphisms_finite (F := F) K
  have hbot : ∀ i ≥ ramificationCutoff T K, lowerGroup T.Integers (inertia T K) i = ⊥ := by
    intro i hi
    change inertiaLowerGroup T K i = ⊥
    rw [inertiaLowerGroup, lowerRamificationGroup_eq_bot_of_cutoff T K i hi,
      Subgroup.bot_subgroupOf]
  have hlg : ∀ j, lowerGroup T.Integers (inertia T K) j = inertiaLowerGroup T K j :=
    fun _ => rfl
  change ((Ramification.swanConductor T.Integers (inertia T K) ρ : ℚ) : ℝ) = _
  rw [Ramification.swanConductor_eq_sum_range T.Integers (inertia T K) ρ _ hbot,
    Rat.cast_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  simp only [conductorTerm, fixedCodimension, hlg, card_inertiaLowerGroup]
  rw [Nat.cast_sub (Submodule.finrank_le _)]
  push_cast
  rfl

/-- Swan sum as the integral of the upper codimension profile. -/
theorem inertiaSwanConductor_eq_integral {B : ℝ}
    (hB : herbrandPhi T K (ramificationCutoff T K) ≤ B) :
    (inertiaSwanConductor T K ρ : ℝ) = ∫ v in (0 : ℝ)..B, upperCodimension T K ρ v := by
  set b := ramificationCutoff T K with hb
  rw [← intervalIntegral.integral_add_adjacent_intervals
    (upperCodimension_intervalIntegrable T K ρ 0 (herbrandPhi T K b))
    (upperCodimension_intervalIntegrable T K ρ _ B)]
  have htail : ∫ v in herbrandPhi T K b..B, upperCodimension T K ρ v = 0 := by
    rw [intervalIntegral.integral_congr (g := fun _ => (0 : ℝ)) ?_]
    · simp
    · intro v hv
      rw [Set.uIcc_of_le hB] at hv
      change upperCodimension T K ρ v = 0
      rw [upperCodimension, inertiaUpperFixedVectors_eq_top T K ρ hv.1, finrank_top, sub_self]
  have hsum := intervalIntegral.sum_integral_adjacent_intervals
    (a := fun k : ℕ => herbrandPhi T K k) (f := upperCodimension T K ρ) (μ := volume)
    (n := b) (fun k _ => upperCodimension_intervalIntegrable T K ρ _ _)
  simp only [Nat.cast_add, Nat.cast_one, Nat.cast_zero, herbrandPhi_zero] at hsum
  rw [htail, add_zero, ← hsum, inertiaSwanConductor_eq_sum T K ρ]
  exact Finset.sum_congr rfl fun i _ => (integral_upperCodimension_step T K ρ i).symm

/-- Artin sum as the tame codimension plus the integral of the profile. -/
theorem inertiaArtinConductor_eq_integral {B : ℝ}
    (hB : herbrandPhi T K (ramificationCutoff T K) ≤ B) :
    (inertiaArtinConductor T K ρ : ℝ) =
      upperCodimension T K ρ 0 + ∫ v in (0 : ℝ)..B, upperCodimension T K ρ v := by
  rw [inertiaArtinConductor_eq_tame_add_swan, Rat.cast_add,
    inertiaSwanConductor_eq_integral T K ρ hB, Rat.cast_natCast]
  congr 1
  rw [upperCodimension, inertiaUpperFixedVectors_zero, fixedCodimension,
    Nat.cast_sub (Submodule.finrank_le _)]

end InertiaConductorRefinement

open InertiaConductorRefinement VirtualRepresentation.LocalWeil.Ramification

universe uF uV

/-- Two finite inertia presentations of the same Weil representation have the same
Artin and Swan sums. -/
theorem presentation_conductors_eq {p : ℕ} [Fact p.Prime] (F : PadicField.{uF} p)
    (A : FiniteRepresentation.{0, uF, uV} ℂ (localWeilGroup F))
    (P Q : FiniteInertiaPresentation F A)
    (hP : Function.Surjective (weilInertiaRestriction F P.extension))
    (hQ : Function.Surjective (weilInertiaRestriction F Q.extension)) :
    P.artinConductor hP = Q.artinConductor hQ ∧ P.swanConductor hP = Q.swanConductor hQ := by
  set TP := (absoluteFiniteExtension F P.extension).canonicalTopologicalData
  set TQ := (absoluteFiniteExtension F Q.extension).canonicalTopologicalData
  have hprof : ∀ v : ℝ, 0 ≤ v →
      upperCodimension TP F.Carrier (P.representation hP) v =
        upperCodimension TQ F.Carrier (Q.representation hQ) v := by
    intro v hv
    simp only [upperCodimension]
    rw [← HerbrandBridge.presentationUpperFixedComparison F A P hP v hv,
      ← HerbrandBridge.presentationUpperFixedComparison F A Q hQ v hv]
  set B := max (herbrandPhi TP F.Carrier (ramificationCutoff TP F.Carrier))
    (herbrandPhi TQ F.Carrier (ramificationCutoff TQ F.Carrier)) with hBdef
  have hB0 : 0 ≤ B := by
    have := (herbrandPhi_strictMono TP F.Carrier).monotone
      (Nat.cast_nonneg (ramificationCutoff TP F.Carrier) : (0 : ℝ) ≤ _)
    rw [herbrandPhi_zero] at this
    exact this.trans (le_max_left _ _)
  have hint : ∫ v in (0 : ℝ)..B, upperCodimension TP F.Carrier (P.representation hP) v =
      ∫ v in (0 : ℝ)..B, upperCodimension TQ F.Carrier (Q.representation hQ) v := by
    apply intervalIntegral.integral_congr
    intro v hv
    rw [Set.uIcc_of_le hB0] at hv
    exact hprof v hv.1
  refine ⟨?_, ?_⟩
  · apply Rat.cast_injective (α := ℝ)
    change (inertiaArtinConductor TP F.Carrier (P.representation hP) : ℝ) =
      (inertiaArtinConductor TQ F.Carrier (Q.representation hQ) : ℝ)
    rw [inertiaArtinConductor_eq_integral TP F.Carrier _ (le_max_left _ _),
      inertiaArtinConductor_eq_integral TQ F.Carrier _ (le_max_right _ _), hint,
      hprof 0 le_rfl]
  · apply Rat.cast_injective (α := ℝ)
    change (inertiaSwanConductor TP F.Carrier (P.representation hP) : ℝ) =
      (inertiaSwanConductor TQ F.Carrier (Q.representation hQ) : ℝ)
    rw [inertiaSwanConductor_eq_integral TP F.Carrier _ (le_max_left _ _),
      inertiaSwanConductor_eq_integral TQ F.Carrier _ (le_max_right _ _), hint]

/-- Enlarging the finite Galois field of an inertia presentation preserves its Artin
and Swan sums. -/
theorem finiteInertiaConductorRefinement {p : ℕ} [Fact p.Prime] (F : PadicField.{uF} p)
    (A : FiniteRepresentation.{0, uF, uV} ℂ (localWeilGroup F)) :
    FiniteInertiaConductorRefinementStatement F A := by
  intro P M h hP hM
  exact presentation_conductors_eq F A (P.refine M h) P hM hP

end Langlands.Ramification.Padic
