import Langlands.LocalFactor.Ramification.LocalWeilBreakStatement
import Langlands.LocalFactor.Ramification.LocalInertiaPresentationProof
import Langlands.LocalFactor.Ramification.Herbrand.LocalAbsoluteInertiaProof
import Langlands.LocalFactor.Ramification.Herbrand.LocalQuotientProof
import Langlands.Weil.Representation.SubquotientContinuity
import Langlands.Weil.Representation.IsomorphismInvarianceProof

/-!
# Upper breaks of local Weil representations

Finite upper fixed spaces recover the upper-break multiplicities. Via the
finite images of the absolute filtration they compute the intrinsic Weil
breaks and the Swan conductor of an irreducible Weil representation.
-/

noncomputable section

namespace Langlands.Ramification.Local

open Module Weil.Local.SepClosed
open VirtualRepresentation.LocalWeil.SepClosed.Ramification
open scoped BigOperators Classical

universe uK uΩ uV uW

/-- Strict positive prefix sums determine a finitely supported multiplicity function
on the nonnegative reals, including its value at zero. -/
private theorem multiplicities_eq_of_prefix_sums {f g : ℝ →₀ ℕ}
    (hf : ∀ x ∈ f.support, 0 ≤ x) (hg : ∀ x ∈ g.support, 0 ≤ x)
    (h : ∀ r : ℝ, 0 < r →
      ∑ x ∈ f.support.filter (· < r), f x = ∑ x ∈ g.support.filter (· < r), g x) :
    f = g := by
  let S := f.support ∪ g.support
  have hfS : f.support ⊆ S := Finset.subset_union_left
  have hgS : g.support ⊆ S := Finset.subset_union_right
  have hnonneg (x : ℝ) (hx : x ∈ S) : 0 ≤ x :=
    (Finset.mem_union.mp hx).elim (hf x) (hg x)
  have extendSum (p : ℝ →₀ ℕ) (hp : p.support ⊆ S) (r : ℝ) :
      ∑ x ∈ p.support.filter (· < r), p x = ∑ x ∈ S.filter (· < r), p x := by
    apply Finset.sum_subset (Finset.filter_subset_filter _ hp)
    intro x hx hxp
    exact Finsupp.notMem_support_iff.mp fun hmem =>
      hxp (Finset.mem_filter.mpr ⟨hmem, (Finset.mem_filter.mp hx).2⟩)
  have hsum (r : ℝ) : ∑ x ∈ S.filter (· < r), f x = ∑ x ∈ S.filter (· < r), g x := by
    by_cases hr : 0 < r
    · rw [← extendSum f hfS, ← extendSum g hgS]
      exact h r hr
    · have hempty : S.filter (· < r) = ∅ := Finset.filter_eq_empty_iff.mpr
        fun x hx => not_lt.mpr ((le_of_not_gt hr).trans (hnonneg x hx))
      simp [hempty]
  ext r
  by_cases hr : r ∈ S
  · obtain ⟨s, hrs, hs⟩ : ∃ s, r < s ∧ ∀ x ∈ S, r < x → s ≤ x := by
      let U := S.filter (r < ·)
      by_cases hU : U.Nonempty
      · exact ⟨U.min' hU, (Finset.mem_filter.mp (U.min'_mem hU)).2,
          fun x hx hrx => U.min'_le x (Finset.mem_filter.mpr ⟨hx, hrx⟩)⟩
      · exact ⟨r + 1, lt_add_one r, fun x hx hrx =>
          (hU ⟨x, Finset.mem_filter.mpr ⟨hx, hrx⟩⟩).elim⟩
    have hfilter : S.filter (· < s) = insert r (S.filter (· < r)) := by
      ext x
      simp only [Finset.mem_filter, Finset.mem_insert]
      constructor
      · rintro ⟨hx, hxs⟩
        rcases lt_trichotomy x r with hxr | rfl | hrx
        · exact Or.inr ⟨hx, hxr⟩
        · exact Or.inl rfl
        · exact (hxs.not_ge (hs x hx hrx)).elim
      · rintro (rfl | ⟨hx, hxr⟩)
        · exact ⟨hr, hrs⟩
        · exact ⟨hx, hxr.trans hrs⟩
    have hnot : r ∉ S.filter (· < r) := by simp
    have hsums := hsum s
    rw [hfilter, Finset.sum_insert hnot, Finset.sum_insert hnot, hsum r] at hsums
    exact Nat.add_right_cancel hsums
  · rw [Finsupp.notMem_support_iff.mp (fun hx => hr (hfS hx)),
      Finsupp.notMem_support_iff.mp (fun hx => hr (hgS hx))]

/-- Dimensions at positive upper indices determine all finite break multiplicities. -/
private theorem upperBreakMultiplicities_eq_of_fixed_finrank
    {K : Type uK} [Field K] [ValuativeRel K] [TopologicalSpace K]
    {L M : Type uΩ} [Field L] [Field M] [Algebra K L] [Algebra K M]
    [FiniteDimensional K L] [FiniteDimensional K M]
    (T : LocalField.TopologicalData K L) (S : LocalField.TopologicalData K M)
    {V : Type uV} [AddCommGroup V] [Module ℂ V] [FiniteDimensional ℂ V]
    {U : Type uW} [AddCommGroup U] [Module ℂ U] [FiniteDimensional ℂ U]
    (ρ : Representation ℂ (inertia T K) V) (σ : Representation ℂ (inertia S K) U)
    (h : ∀ r : ℝ, 0 < r → finrank ℂ (inertiaUpperFixedVectors T K ρ r) =
      finrank ℂ (inertiaUpperFixedVectors S K σ r)) :
    upperBreakMultiplicities T K ρ = upperBreakMultiplicities S K σ :=
  multiplicities_eq_of_prefix_sums (fun _ => upperBreakSupport_nonneg T K ρ)
    (fun _ => upperBreakSupport_nonneg S K σ) fun r hr =>
      (sum_upperBreakSupport_lt T K ρ hr).trans
        ((h r hr).trans (sum_upperBreakSupport_lt S K σ hr).symm)

section Comparisons

variable (K : Type uK) [Field K] [ValuativeRel K] [TopologicalSpace K]
  [IsNonarchimedeanLocalField K]
  (Ω : Type uΩ) [Field Ω] [Algebra K Ω] [IsSepClosure K Ω]

private local instance : NontriviallyNormedField K := LocalGalois.localNormedField K
private local instance : IsUltrametricDist K := LocalGalois.localNormedField_ultrametric K
private local instance : CompleteSpace K := LocalGalois.localNormedField_complete K

local notation "finiteData" => SepClosed.finiteTopologicalData K Ω
local notation "W" =>
  (@localWeilGroup K _ _ _ _ Ω _ _ _ (IsSepClosure.sep_closed K))
local notation "weilProjection" =>
  (@localProjection K _ _ _ _ Ω _ _ _ (IsSepClosure.sep_closed K))
local notation "inertiaInclusion" =>
  (@localInertiaInclusion K _ _ _ _ Ω _ _ _ (IsSepClosure.sep_closed K))
local notation "absoluteUpperInInertia[" r "]" =>
  Subgroup.subgroupOf (localAbsoluteUpperRamificationGroup K Ω r)
    (LocalGalois.SepClosed.absoluteInertia K Ω)
local notation "finiteUpperInInertia[" L ", " r "]" =>
  Subgroup.subgroupOf (localUpperRamificationGroup K L r) (inertia (finiteData L) K)

private theorem absoluteUpper_le_inertia {r : ℝ} (hr : 0 ≤ r) :
    localAbsoluteUpperRamificationGroup K Ω r ≤ LocalGalois.SepClosed.absoluteInertia K Ω :=
  (localAbsoluteUpperRamificationGroup_antitone K Ω hr).trans
    (le_of_eq (absoluteUpperInertia K Ω))

/-- The absolute upper group inside inertia maps onto the finite upper group. -/
private theorem map_absoluteUpperInInertia (L : FiniteGaloisIntermediateField K Ω)
    {r : ℝ} (hr : 0 ≤ r) :
    (absoluteUpperInInertia[r]).map (SepClosed.absoluteInertiaRestriction K Ω L).toMonoidHom =
      finiteUpperInInertia[L, r] := by
  have hfin : localUpperRamificationGroup K L r ≤ inertia (finiteData L) K := by
    rw [← upperRamificationGroup_zero (finiteData L) K]
    exact upperRamificationGroup_antitone (finiteData L) K hr
  apply Subgroup.map_injective (inertia (finiteData L) K).subtype_injective
  rw [Subgroup.map_subgroupOf_eq_of_le hfin, Subgroup.map_map]
  change (absoluteUpperInInertia[r]).map
      ((absoluteFiniteRestriction K Ω L).toMonoidHom.comp
        (LocalGalois.SepClosed.absoluteInertia K Ω).subtype) = localUpperRamificationGroup K L r
  rw [← Subgroup.map_map, Subgroup.map_subgroupOf_eq_of_le (absoluteUpper_le_inertia K Ω hr)]
  exact Wintenberger.localAbsoluteUpperFiniteImage K Ω L r (by linarith)

private theorem map_finiteUpperInInertia {L M : FiniteGaloisIntermediateField K Ω} (h : L ≤ M)
    {r : ℝ} (hr : 0 ≤ r) :
    (finiteUpperInInertia[M, r]).map (SepClosed.finiteInertiaRestriction K Ω h).toMonoidHom =
      finiteUpperInInertia[L, r] := by
  have hcomp : (SepClosed.finiteInertiaRestriction K Ω h).toMonoidHom.comp
      (SepClosed.absoluteInertiaRestriction K Ω M).toMonoidHom =
        (SepClosed.absoluteInertiaRestriction K Ω L).toMonoidHom :=
    MonoidHom.ext (finiteInertiaRestriction_absolute K K Ω _ _ h)
  rw [← map_absoluteUpperInInertia K Ω M hr, Subgroup.map_map, hcomp,
    map_absoluteUpperInInertia K Ω L hr]

/-- Finite upper multiplicities and support are preserved by inflation. -/
theorem finiteUpperBreakInflation : FiniteUpperBreakInflation.{uK, uΩ, uV} K Ω := by
  intro L M h V _ _ _ ρ
  let π := (SepClosed.finiteInertiaRestriction K Ω h).toMonoidHom
  have hmul : upperBreakMultiplicities (finiteData M) K (ρ.comp π) =
      upperBreakMultiplicities (finiteData L) K ρ := by
    apply upperBreakMultiplicities_eq_of_fixed_finrank (finiteData M) (finiteData L) (ρ.comp π) ρ
    intro r hr
    change finrank ℂ (fixedVectors (ρ.comp π) (finiteUpperInInertia[M, r])) =
      finrank ℂ (fixedVectors ρ (finiteUpperInInertia[L, r]))
    rw [fixedVectors_comp_eq_map, map_finiteUpperInInertia K Ω h hr.le]
  exact ⟨hmul, congrArg Finsupp.support hmul⟩

private theorem map_absoluteUpperInInertia_to_weil {r : ℝ} (hr : 0 ≤ r) :
    (absoluteUpperInInertia[r]).map (inertiaInclusion).toMonoidHom = upperGroup K Ω r := by
  let : IsSepClosed Ω := IsSepClosure.sep_closed K
  ext w
  rw [Subgroup.mem_map, mem_upperGroup]
  constructor
  · rintro ⟨σ, hσ, rfl⟩
    exact hσ
  · intro hw
    let σ : LocalGalois.SepClosed.absoluteInertia K Ω :=
      ⟨weilProjection w, absoluteUpper_le_inertia K Ω hr hw⟩
    exact ⟨σ, hw, Weil.projection_injective _ rfl⟩

/-- Each finite presentation computes the intrinsic nonnegative upper fixed spaces. -/
theorem presentationUpperFixedComparison : PresentationUpperFixedComparison.{uK, uΩ, uV} K Ω := by
  let : IsSepClosed Ω := IsSepClosure.sep_closed K
  intro A P hP r hr
  let H := absoluteUpperInInertia[r]
  let π := (SepClosed.absoluteInertiaRestriction K Ω P.extension).toMonoidHom
  have hAction : A.representation.comp (inertiaInclusion).toMonoidHom = (P.representation hP).comp π := by
    apply MonoidHom.ext
    intro σ
    let w : localInertia K Ω := ⟨inertiaInclusion σ, rfl⟩
    exact (FiniteInertiaPresentation.representation_apply P hP w).symm
  calc
    _ = fixedVectors A.representation (H.map (inertiaInclusion).toMonoidHom) :=
      congrArg (fixedVectors A.representation) (map_absoluteUpperInInertia_to_weil K Ω hr).symm
    _ = fixedVectors (A.representation.comp (inertiaInclusion).toMonoidHom) H :=
      (fixedVectors_comp_eq_map _ _ H).symm
    _ = fixedVectors ((P.representation hP).comp π) H := congrArg (fun ρ => fixedVectors ρ H) hAction
    _ = fixedVectors (P.representation hP) (H.map π) := fixedVectors_comp_eq_map _ _ H
    _ = _ := congrArg (fixedVectors (P.representation hP))
      (map_absoluteUpperInInertia K Ω P.extension hr)

/-- Equivalent Weil actions have equal multiplicities and support at any presentations. -/
theorem presentationUpperBreakEquivalence : PresentationUpperBreakEquivalence.{uK, uΩ, uV, uW} K Ω := by
  intro A B ⟨e⟩ P Q hP hQ
  let ρ := P.representation hP
  let σ := Q.representation hQ
  have hmul : upperBreakMultiplicities (finiteData P.extension) K ρ =
      upperBreakMultiplicities (finiteData Q.extension) K σ := by
    apply upperBreakMultiplicities_eq_of_fixed_finrank (finiteData P.extension)
      (finiteData Q.extension) ρ σ
    intro r hr
    calc
      _ = finrank ℂ (upperFixedSpace K Ω A r) :=
        congrArg (fun X : Submodule ℂ A => finrank ℂ X)
          (presentationUpperFixedComparison K Ω A P hP r hr.le).symm
      _ = finrank ℂ (upperFixedSpace K Ω B r) :=
        (fixedVectorsEquiv e (upperGroup K Ω r)).finrank_eq
      _ = _ := congrArg (fun X : Submodule ℂ B => finrank ℂ X)
        (presentationUpperFixedComparison K Ω B Q hQ r hr.le)
  exact ⟨hmul, congrArg Finsupp.support hmul⟩

/-- Two presentations of the same Weil action have the same breaks. -/
theorem presentationUpperBreakIndependence : PresentationUpperBreakIndependence.{uK, uΩ, uV} K Ω := by
  intro A P Q hP hQ
  exact presentationUpperBreakEquivalence K Ω A A ⟨Representation.Equiv.refl _⟩ P Q hP hQ

/-- Refining a presentation preserves its upper-break multiplicities. -/
theorem presentationUpperBreakRefinement : PresentationUpperBreakRefinement.{uK, uΩ, uV} K Ω := by
  intro A P M h hP hM
  exact (presentationUpperBreakIndependence K Ω A (P.refine M h) P hM hP).1

end Comparisons

section Swan

variable {K : Type uK} [Field K] [ValuativeRel K] [TopologicalSpace K]
  {L : Type uΩ} [Field L] [Algebra K L] [FiniteDimensional K L]
  (T : LocalField.TopologicalData K L)

/-- The width of the upper interval corresponding to the lower interval `(i, i+1]`. -/
private theorem herbrandPhi_step_width (i : ℕ) :
    herbrandPhi T K ((i + 1 : ℕ) : ℝ) - herbrandPhi T K i =
      (lowerGroupOrder T K (i + 1) : ℝ) / lowerGroupOrder T K 0 := by
  have h (n : ℕ) : herbrandPhi T K n =
      (∑ j ∈ Finset.range n, (lowerGroupOrder T K (j + 1) : ℝ)) / lowerGroupOrder T K 0 := by
    rw [herbrandPhi_floor T K (Nat.cast_nonneg n), Nat.floor_natCast, sub_self, zero_mul, add_zero]
  rw [h, h, Finset.sum_range_succ, ← sub_div, add_sub_cancel_left]

omit [FiniteDimensional K L] in
private theorem card_inertiaLowerGroup (i : ℕ) :
    Nat.card (inertiaLowerGroup T K i) = lowerGroupOrder T K i := by
  have hle : lowerRamificationGroup T K i ≤ inertia T K := by
    rw [← lowerRamificationGroup_zero]
    exact lowerRamificationGroup_antitone T K (Nat.zero_le i)
  exact Nat.card_congr (Subgroup.subgroupOfEquivOfLe hle).toEquiv

variable {V : Type uV} [AddCommGroup V] [Module ℂ V] [FiniteDimensional ℂ V]
  (ρ : Representation ℂ (inertia T K) V)

private theorem inertiaSwanConductor_eq_sum :
    (inertiaSwanConductor T K ρ : ℝ) =
      ∑ i ∈ Finset.range (ramificationCutoff T K),
        (lowerGroupOrder T K (i + 1) : ℝ) / lowerGroupOrder T K 0 *
          (fixedCodimension _ ρ (inertiaLowerGroup T K (i + 1)) : ℝ) := by
  let := inertiaIntegerAction T K
  have : IsNoetherianRing T.Integers := by
    let := T.topology
    let := T.valuativeRel
    let := T.localField
    infer_instance
  have : FaithfulSMul (inertia T K) T.Integers := by
    let := integerAction T K
    have := QuotientBridge.integerAction_faithful T K
    exact ⟨fun h => Subtype.ext (FaithfulSMul.eq_of_smul_eq_smul (α := T.Integers) h)⟩
  have hbot (i : ℕ) (hi : ramificationCutoff T K ≤ i) :
      lowerGroup T.Integers (inertia T K) i = ⊥ := by
    change inertiaLowerGroup T K i = ⊥
    rw [inertiaLowerGroup, lowerRamificationGroup_eq_bot_of_cutoff T K i hi,
      Subgroup.bot_subgroupOf]
  have hcard (i : ℕ) : Nat.card (lowerGroup T.Integers (inertia T K) i) = lowerGroupOrder T K i :=
    card_inertiaLowerGroup T i
  rw [inertiaSwanConductor, Ramification.swanConductor_eq_sum_range _ _ _ _ hbot, Rat.cast_sum]
  simp only [conductorTerm, hcard, Rat.cast_mul, Rat.cast_div, Rat.cast_natCast]
  rfl

/-- Summation by parts for the Swan sum up to a finite lower index. -/
private theorem sum_swan_eq_sum_weighted_lowerBreaks (n : ℕ) :
    let φ := fun i : ℕ => herbrandPhi T K i
    let d := inertiaFixedDimension T K ρ
    let D := (finrank ℂ V : ℝ)
    (∑ i ∈ Finset.range n, (φ (i + 1) - φ i) * (D - (d (i + 1) : ℝ))) =
      (∑ i ∈ Finset.range (n + 1), φ i * (lowerBreakMultiplicity T K ρ i : ℝ)) +
        φ n * (D - (d (n + 1) : ℝ)) := by
  dsimp only
  induction n with
  | zero => simp [herbrandPhi_zero]
  | succ n ih =>
    rw [Finset.sum_range_succ, ih, Finset.sum_range_succ (n := n + 1),
      lowerBreakMultiplicity_pos_index T K ρ (Nat.succ_pos n),
      Nat.cast_sub (inertiaFixedDimension_monotone T K ρ (Nat.le_succ (n + 1)))]
    ring

private theorem inertiaSwanConductor_eq_weighted_breaks :
    (inertiaSwanConductor T K ρ : ℝ) =
      ∑ r ∈ upperBreakSupport T K ρ, r * (upperBreakMultiplicities T K ρ r : ℝ) := by
  let n := ramificationCutoff T K
  have hfull : inertiaFixedDimension T K ρ (n + 1) = finrank ℂ V :=
    inertiaFixedDimension_of_cutoff T K ρ (Nat.le_succ n)
  calc
    _ = ∑ i ∈ Finset.range n,
        (herbrandPhi T K ((i + 1 : ℕ) : ℝ) - herbrandPhi T K i) *
          ((finrank ℂ V : ℝ) - (inertiaFixedDimension T K ρ (i + 1) : ℝ)) := by
      rw [inertiaSwanConductor_eq_sum T ρ]
      apply Finset.sum_congr rfl
      intro i _
      have hcod : (fixedCodimension _ ρ (inertiaLowerGroup T K (i + 1)) : ℝ) =
          (finrank ℂ V : ℝ) - (inertiaFixedDimension T K ρ (i + 1) : ℝ) :=
        Nat.cast_sub (inertiaFixedDimension_le_rank T K ρ (i + 1))
      rw [herbrandPhi_step_width, hcod]
    _ = ∑ i ∈ Finset.range (n + 1), herbrandPhi T K i * (lowerBreakMultiplicity T K ρ i : ℝ) := by
      simpa only [hfull, sub_self, mul_zero, add_zero] using
        sum_swan_eq_sum_weighted_lowerBreaks T ρ n
    _ = _ := by
      rw [upperBreakSupport_eq_map, Finset.sum_map]
      simp only [upperBreakIndex_apply, upperBreakMultiplicities_phi]
      symm
      apply Finset.sum_subset
      · intro i hi
        by_contra h
        have hni : n + 1 ≤ i := Nat.le_of_not_lt (fun hlt => h (Finset.mem_range.mpr hlt))
        have hz := lowerBreakMultiplicity_eq_zero_of_lower_eq_bot T K ρ
          (by omega) (lowerRamificationGroup_eq_bot_of_cutoff T K i (by omega))
        exact (Finsupp.mem_support_iff.mp hi) hz
      · intro i _ hi
        have hz : lowerBreakMultiplicity T K ρ i = 0 := Finsupp.notMem_support_iff.mp hi
        simp [hz]

end Swan

section Weil

variable (K : Type uK) [Field K] [ValuativeRel K] [TopologicalSpace K]
  [IsNonarchimedeanLocalField K]
  (Ω : Type uΩ) [Field Ω] [Algebra K Ω] [IsSepClosure K Ω]

local notation "finiteData" => SepClosed.finiteTopologicalData K Ω
local notation "W" =>
  (@localWeilGroup K _ _ _ _ Ω _ _ _ (IsSepClosure.sep_closed K))

/-- The Swan conductor is the sum of upper breaks weighted by multiplicity. -/
theorem finiteUpperBreakWeightedSwan : FiniteUpperBreakWeightedSwan.{uK, uΩ, uV} K Ω := by
  intro L V _ _ _ ρ
  exact inertiaSwanConductor_eq_weighted_breaks (finiteData L) ρ

/-- At a finite inertia level, the Artin sum adds the codimension of the inertia invariants. -/
theorem finiteUpperBreakArtinIdentity : FiniteUpperBreakArtinIdentity.{uK, uΩ, uV} K Ω := by
  intro L V _ _ _ ρ
  exact (inertiaArtinConductor_eq_tame_add_swan (finiteData L) K ρ).trans (add_comm _ _)

/-- The upper fixed space is full precisely when the upper action is trivial. -/
private theorem upperFixedSpace_eq_top_iff
    (A : FiniteRepresentation.{0, uΩ, uV} ℂ W) (r : ℝ) :
    upperFixedSpace K Ω A r = ⊤ ↔ IsTrivialAt K Ω A r := by
  constructor
  · intro h w hw
    apply LinearMap.ext
    intro v
    have hv : v ∈ upperFixedSpace K Ω A r := h ▸ Submodule.mem_top
    exact (mem_upperFixedSpace K Ω A r v).mp hv w hw
  · intro h
    apply eq_top_iff.mpr
    intro v _
    rw [mem_upperFixedSpace]
    intro w hw
    rw [h w hw]
    rfl

private theorem maximumUpperBreak_lt_iff_isTrivialAt
    (A : FiniteRepresentation.{0, uΩ, uV} ℂ W)
    (P : SepClosed.FiniteInertiaPresentation K Ω A)
    (hP : Function.Surjective (SepClosed.weilInertiaRestriction K Ω P.extension))
    (hne : (upperBreakSupport (finiteData P.extension) K (P.representation hP)).Nonempty)
    {b : ℝ} (hb : 0 < b) :
    maximumUpperBreak (finiteData P.extension) K (P.representation hP) hne < b ↔
      IsTrivialAt K Ω A b := by
  refine (maximumUpperBreak_lt_iff_fixed_eq_top (finiteData P.extension) K (P.representation hP)
    hne hb).trans ?_
  rw [← presentationUpperFixedComparison K Ω A P hP b hb.le]
  exact upperFixedSpace_eq_top_iff K Ω A b

/-- A finite presentation gives a nonnegative bound that is strict exactly at
its positive triviality thresholds. The zero-dimensional action has bound zero. -/
private theorem exists_triviality_bound
    (A : FiniteRepresentation.{0, uΩ, uV} ℂ W)
    (P : SepClosed.FiniteInertiaPresentation K Ω A)
    (hP : Function.Surjective (SepClosed.weilInertiaRestriction K Ω P.extension)) :
    ∃ m : ℝ, 0 ≤ m ∧ ∀ b : ℝ, 0 < b → (m < b ↔ IsTrivialAt K Ω A b) := by
  by_cases hne : (upperBreakSupport (finiteData P.extension) K (P.representation hP)).Nonempty
  · exact ⟨_, maximumUpperBreak_nonneg (finiteData P.extension) K (P.representation hP) hne,
      fun _ hb => maximumUpperBreak_lt_iff_isTrivialAt K Ω A P hP hne hb⟩
  · have hz : A.rank = 0 := (upperBreakSupport_eq_empty_iff _ _ _).mp
      (Finset.not_nonempty_iff_eq_empty.mp hne)
    have : Subsingleton A := Module.finrank_zero_iff.mp hz
    exact ⟨0, le_rfl, fun _ hb => iff_of_true hb (fun _ _ =>
      LinearMap.ext fun _ => Subsingleton.elim _ _)⟩

private theorem mem_trivialityThresholds_of_bound
    (A : FiniteRepresentation.{0, uΩ, uV} ℂ W) {m b : ℝ} (hm : 0 ≤ m)
    (h : ∀ r : ℝ, 0 < r → (m < r ↔ IsTrivialAt K Ω A r)) (hb : m < b) :
    b ∈ trivialityThresholds K Ω A :=
  ⟨(hm.trans_lt hb).le, (h b (hm.trans_lt hb)).mp hb⟩

/-- A bound characterizing triviality at positive indices is the infimum of all thresholds. -/
private theorem lastBreak_eq_of_triviality_bound
    (A : FiniteRepresentation.{0, uΩ, uV} ℂ W) {m : ℝ} (hm : 0 ≤ m)
    (h : ∀ r : ℝ, 0 < r → (m < r ↔ IsTrivialAt K Ω A r)) : lastBreak K Ω A = m := by
  apply le_antisymm
  · apply le_of_forall_pos_lt_add
    intro ε hε
    obtain ⟨b, hb, hbε⟩ := exists_between (lt_add_of_pos_right m hε)
    exact (lastBreak_le_of_mem K Ω A (mem_trivialityThresholds_of_bound K Ω A hm h hb)).trans_lt hbε
  · change m ≤ sInf (trivialityThresholds K Ω A)
    refine le_csInf ⟨m + 1, mem_trivialityThresholds_of_bound K Ω A hm h (lt_add_one m)⟩ ?_
    intro b hb
    have hb0 : 0 ≤ b := hb.1
    apply le_of_forall_pos_lt_add
    intro ε hε
    exact (h (b + ε) (by linarith)).mpr
      (isTrivialAt_mono K Ω A (le_add_of_nonneg_right hε.le) hb.2)

/-- Continuity supplies a finite presentation and hence a nonnegative triviality threshold. -/
theorem weilTrivialityThresholdsNonempty : WeilTrivialityThresholdsNonempty.{uK, uΩ, uV} K Ω := by
  intro A hA
  obtain ⟨P⟩ := continuousWeilFiniteInertiaPresentation K Ω A hA
  obtain ⟨m, hm, h⟩ := exists_triviality_bound K Ω A P
    (weilInertiaRestrictionSurjectivity K Ω P.extension)
  exact ⟨m + 1, mem_trivialityThresholds_of_bound K Ω A hm h (lt_add_one m)⟩

private theorem lastBreak_lt_iff_isTrivialAt
    (A : FiniteRepresentation.{0, uΩ, uV} ℂ W) (hA : A.IsContinuous) {b : ℝ} (hb : 0 < b) :
    lastBreak K Ω A < b ↔ IsTrivialAt K Ω A b := by
  obtain ⟨P⟩ := continuousWeilFiniteInertiaPresentation K Ω A hA
  obtain ⟨m, hm, h⟩ := exists_triviality_bound K Ω A P
    (weilInertiaRestrictionSurjectivity K Ω P.extension)
  rw [lastBreak_eq_of_triviality_bound K Ω A hm h]
  exact h b hb

/-- The last break is the maximum of the finite break support in positive rank. -/
theorem weilLastBreakFiniteMaximum : WeilLastBreakFiniteMaximum.{uK, uΩ, uV} K Ω := by
  intro A _ hrank P hP
  let T := finiteData P.extension
  let ρ := P.representation hP
  have hne : (upperBreakSupport T K ρ).Nonempty := (upperBreakSupport_nonempty_iff T K ρ).mpr hrank
  exact ⟨hne, lastBreak_eq_of_triviality_bound K Ω A (maximumUpperBreak_nonneg T K ρ hne)
    fun _ hb => maximumUpperBreak_lt_iff_isTrivialAt K Ω A P hP hne hb⟩

/-- The last break is zero exactly when the positive upper groups act trivially. -/
theorem weilLastBreakZero : WeilLastBreakZero.{uK, uΩ, uV} K Ω := by
  intro A hA
  constructor
  · intro h r hr
    exact (lastBreak_lt_iff_isTrivialAt K Ω A hA hr).mp (h ▸ hr)
  · intro h
    apply le_antisymm _ (lastBreak_nonneg K Ω A)
    apply le_of_forall_pos_lt_add
    intro ε hε
    rw [zero_add]
    exact (lastBreak_lt_iff_isTrivialAt K Ω A hA hε).mpr (h ε hε)

/-- Normality makes the upper fixed space a Weil subrepresentation. -/
private theorem upperFixedSpace_eq_bot_or_eq_top
    (A : FiniteRepresentation.{0, uΩ, uV} ℂ W) (hirr : A.IsIrreducible) (r : ℝ) :
    upperFixedSpace K Ω A r = ⊥ ∨ upperFixedSpace K Ω A r = ⊤ := by
  let : IsSepClosed Ω := IsSepClosure.sep_closed K
  have hn : (upperGroup K Ω r).Normal := (localAbsoluteUpperRamificationGroup_normal K Ω r).comap _
  let S : Subrepresentation A.representation :=
    { toSubmodule := upperFixedSpace K Ω A r
      apply_mem_toSubmodule := by
        intro g v hv
        rw [mem_upperFixedSpace] at hv ⊢
        intro w hw
        have hc : g⁻¹ * w * g ∈ upperGroup K Ω r := by
          simpa using hn.conj_mem w hw g⁻¹
        have hsplit : w * g = g * (g⁻¹ * w * g) := by group
        rw [← Module.End.mul_apply, ← map_mul, hsplit, map_mul, Module.End.mul_apply, hv _ hc] }
  have : IsSimpleOrder (Subrepresentation A.representation) := hirr
  rcases IsSimpleOrder.eq_bot_or_eq_top S with h | h
  · exact Or.inl (congrArg Subrepresentation.toSubmodule h)
  · exact Or.inr (congrArg Subrepresentation.toSubmodule h)

/-- Positive indices through the last break have no irreducible fixed vectors.
Strictly larger indices have the full space. -/
theorem weilIrreduciblePositiveThresholds : WeilIrreduciblePositiveThresholds.{uK, uΩ, uV} K Ω := by
  intro A hA hirr
  have htop (r : ℝ) (hr : 0 < r) :
      lastBreak K Ω A < r ↔ upperFixedSpace K Ω A r = ⊤ :=
    (lastBreak_lt_iff_isTrivialAt K Ω A hA hr).trans (upperFixedSpace_eq_top_iff K Ω A r).symm
  refine ⟨fun a ha => ⟨fun hle => ?_, fun hbot => ?_⟩, htop⟩
  · rcases upperFixedSpace_eq_bot_or_eq_top K Ω A hirr a with h | h
    · exact h
    · exact (hle.not_gt ((htop a ha).mpr h)).elim
  · by_contra! hlt
    have : IsSimpleOrder (Subrepresentation A.representation) := hirr
    have hbt : (⊥ : Subrepresentation A.representation) = ⊤ :=
      Subrepresentation.toSubmodule_injective (hbot.symm.trans ((htop a ha).mp hlt))
    exact bot_ne_top hbt

/-- An irreducible Weil representation has a single upper break of full rank. -/
theorem weilIrreducibleUpperBreak : WeilIrreducibleUpperBreak.{uK, uΩ, uV} K Ω := by
  intro A hA hirr P hP
  let T := finiteData P.extension
  let ρ := P.representation hP
  have hrank : 0 < A.rank := by
    have : IsSimpleModule (MonoidAlgebra ℂ W) A.representation.asModule :=
      (Representation.irreducible_iff_isSimpleModule_asModule _).mp hirr
    have : Nontrivial A := IsSimpleModule.nontrivial (MonoidAlgebra ℂ W) A.representation.asModule
    exact Module.finrank_pos
  obtain ⟨hne, hmax⟩ := weilLastBreakFiniteMaximum K Ω A hA hrank P hP
  have hmin : minimumUpperBreak T K ρ hne = lastBreak K Ω A := by
    apply le_antisymm
    · rw [hmax]
      exact minimumUpperBreak_le_maximumUpperBreak T K ρ hne
    · rcases (lastBreak_nonneg K Ω A).eq_or_lt with h0 | hpos
      · rw [← h0]
        exact minimumUpperBreak_nonneg T K ρ hne
      · have hbot := ((weilIrreduciblePositiveThresholds K Ω A hA hirr).1 _ hpos).mp le_rfl
        exact (le_minimumUpperBreak_iff_fixed_eq_bot T K ρ hne hpos).mpr
          ((presentationUpperFixedComparison K Ω A P hP _ hpos.le).symm.trans hbot)
  have hsupp : upperBreakSupport T K ρ = {lastBreak K Ω A} := by
    apply Finset.eq_singleton_iff_unique_mem.mpr
    refine ⟨?_, fun r hr => le_antisymm ?_ ?_⟩
    · rw [hmax]
      exact maximumUpperBreak_mem T K ρ hne
    · rw [hmax]
      exact le_maximumUpperBreak T K ρ hne hr
    · rw [← hmin]
      exact minimumUpperBreak_le T K ρ hne hr
  refine ⟨Finsupp.eq_single_iff.mpr ⟨hsupp.le, ?_⟩, hsupp⟩
  have hsum := sum_upperBreakSupport T K ρ
  rwa [hsupp, Finset.sum_singleton] at hsum

/-- The Swan conductor of an irreducible action is its rank times its last break. -/
theorem weilIrreducibleSwanBreak : WeilIrreducibleSwanBreak.{uK, uΩ, uV} K Ω := by
  intro A hA hirr P hP
  obtain ⟨hmul, hsupp⟩ := weilIrreducibleUpperBreak K Ω A hA hirr P hP
  change (inertiaSwanConductor (finiteData P.extension) K (P.representation hP) : ℝ) = _
  rw [finiteUpperBreakWeightedSwan K Ω P.extension A (P.representation hP), hsupp, hmul,
    Finset.sum_singleton, Finsupp.single_eq_same, mul_comm]

set_option maxHeartbeats 800000 in
/-- The class rank and break label recover the formulas for every representative. -/
theorem weilClassBreakComparison : WeilClassBreakComparison.{uK, uΩ, uV} K Ω := by
  intro b A hclassA
  let R := (Quotient.out b.2.val).val
  have hR := (Quotient.out b.2.val).property
  have hclassR : FiniteRepresentation.classOf R = VirtualRepresentation.Weil.underlyingClass W b := by
    exact congrArg (FiniteRepresentation.forgetPropertyClass _) (Quotient.out_eq b.2.val)
  obtain ⟨e⟩ := (FiniteRepresentation.classOf_eq_iff A R).mp (hclassA.trans hclassR.symm)
  have hA : A.IsContinuous := (FiniteRepresentation.isContinuous_iff_of_equiv e).mpr hR.1
  have hirr : A.IsIrreducible := (Weil.IsomorphismInvariance.irreducible_iff e).mpr hR.2
  have hlab : lastBreak K Ω A = breakLabel K Ω b := by
    change lastBreak K Ω A = classLastBreak K Ω (VirtualRepresentation.Weil.underlyingClass W b)
    rw [← hclassA, classLastBreak_classOf]
  have hrank : A.rank = (b.1 : ℕ) := by
    rw [← FiniteRepresentation.classRank_classOf, hclassA]
    exact b.2.property
  have hthresholds := weilIrreduciblePositiveThresholds K Ω A hA hirr
  have hzero := weilLastBreakZero K Ω A hA
  rw [hlab] at hthresholds hzero
  refine ⟨weilTrivialityThresholdsNonempty K Ω A hA, hlab, hrank, hthresholds.1, hthresholds.2, hzero,
    fun P hP => ?_⟩
  obtain ⟨hmul, hsupp⟩ := weilIrreducibleUpperBreak K Ω A hA hirr P hP
  have hswan := weilIrreducibleSwanBreak K Ω A hA hirr P hP
  rw [hlab, hrank] at hmul hswan
  rw [hlab] at hsupp
  exact ⟨hmul, hsupp, hswan⟩

end Weil

/-- Upper breaks and Swan conductors over nonarchimedean local fields, in four
independent universes. -/
theorem weilBreakComparison : WeilBreakComparisonStatement.{uK, uΩ, uV, uW} := by
  intro K _ _ _ _ Ω _ _ _
  exact ⟨finiteUpperBreakInflation K Ω, presentationUpperBreakRefinement K Ω,
    presentationUpperBreakIndependence K Ω, presentationUpperBreakEquivalence K Ω,
    finiteUpperBreakWeightedSwan K Ω, finiteUpperBreakArtinIdentity K Ω,
    presentationUpperFixedComparison K Ω, weilTrivialityThresholdsNonempty K Ω,
    weilLastBreakFiniteMaximum K Ω, weilIrreducibleUpperBreak K Ω, weilIrreducibleSwanBreak K Ω,
    weilIrreduciblePositiveThresholds K Ω, weilLastBreakZero K Ω, weilClassBreakComparison K Ω⟩

end Langlands.Ramification.Local
