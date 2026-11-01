import Langlands.Representation.RankinSelberg.AdjacentRankCompactAverage
import Langlands.HarmonicAnalysis.RectangularTestSmooth
import Mathlib.Topology.Compactness.SigmaCompact
import Mathlib.Topology.Separation.Profinite

/-! Compact open cutoffs inside the full-row-rank rectangular locus. -/

noncomputable section

namespace Langlands.RankinSelberg

open Set Filter Topology HarmonicAnalysis Matrix

universe uF

section Exhaustion

variable {X : Type*} [TopologicalSpace X] [T2Space X] [LocallyCompactSpace X]
  [TotallyDisconnectedSpace X] [SecondCountableTopology X]

/-- An open subset of a locally compact totally disconnected second-countable
Hausdorff space is exhausted by compact clopen ambient subsets. -/
theorem exists_compactClopen_exhaustion_open {U : Set X} (hU : IsOpen U) :
    ∃ C : ℕ → Set X,
      (∀ n, IsCompact (C n) ∧ IsClopen (C n) ∧ C n ⊆ U) ∧ Monotone C ∧
      ∀ x ∈ U, ∀ᶠ n in atTop, x ∈ C n := by
  classical
  let : LocallyCompactSpace U := hU.locallyCompactSpace
  have hpoint (x : U) : ∃ C : Set X, IsCompact C ∧ IsClopen C ∧ x.val ∈ C ∧ C ⊆ U := by
    obtain ⟨D, hDc, hxD, hDU⟩ := exists_compact_subset hU x.property
    obtain ⟨C, hCcl, hxC, hCD⟩ :=
      loc_compact_Haus_tot_disc_of_zero_dim.mem_nhds_iff.mp
        (isOpen_interior.mem_nhds hxD)
    exact ⟨C, hDc.of_isClosed_subset hCcl.isClosed (hCD.trans interior_subset),
      hCcl, hxC, hCD.trans (interior_subset.trans hDU)⟩
  choose D hDc hDcl hxD hDU using hpoint
  have hfinite (n : ℕ) : ∃ C : Set X,
      IsCompact C ∧ IsClopen C ∧ C ⊆ U ∧
        compactCovering U n ⊆ Subtype.val ⁻¹' C := by
    obtain ⟨t, ht⟩ := (isCompact_compactCovering U n).elim_finite_subcover
      (fun x => Subtype.val ⁻¹' D x)
      (fun x => (hDcl x).isOpen.preimage continuous_subtype_val)
      (fun x _ => mem_iUnion.mpr ⟨x, hxD x⟩)
    refine ⟨⋃ x ∈ t, D x, t.isCompact_biUnion (fun x _ => hDc x),
      isClopen_biUnion_finset (fun x _ => hDcl x), ?_, ?_⟩
    · exact iUnion₂_subset fun x _ => hDU x
    · intro x hx
      simpa only [preimage_iUnion] using ht hx
  choose C hCc hCcl hCU hKC using hfinite
  refine ⟨accumulate C, fun n => ⟨isCompact_accumulate hCc n,
    (finite_le_nat n).isClopen_biUnion (fun i _ => hCcl i),
    iUnion₂_subset fun i _ => hCU i⟩, monotone_accumulate, ?_⟩
  intro x hx
  obtain ⟨m, hm⟩ := exists_mem_compactCovering (⟨x, hx⟩ : U)
  filter_upwards [eventually_ge_atTop m] with n hn
  exact mem_iUnion₂.mpr ⟨m, hn, hKC m hm⟩

end Exhaustion

section Rectangular

variable {K : Type uF} [Field K] [TopologicalSpace K]
  [IsTopologicalDivisionRing K] [T2Space K] {n : ℕ}

/-- The right-invertible rectangular locus is open, including the zero-row case. -/
theorem isOpen_adjacentRankFullRank :
    IsOpen {M : Matrix (Fin n) (Fin (n + 1)) K | AdjacentRankFullRank M} := by
  classical
  rw [isOpen_iff_mem_nhds]
  rintro M ⟨R, hR⟩
  have ho : IsOpen {N : Matrix (Fin n) (Fin (n + 1)) K | (N * R).det ≠ 0} :=
    isOpen_ne_fun ((continuous_id.matrix_mul continuous_const).matrix_det) continuous_const
  have hm : M ∈ {N : Matrix (Fin n) (Fin (n + 1)) K | (N * R).det ≠ 0} := by
    simp [hR]
  apply Filter.mem_of_superset (ho.mem_nhds hm)
  intro N hN
  have hi : IsUnit (N * R) := (Matrix.isUnit_iff_isUnit_det _).mpr (Ne.isUnit hN)
  refine ⟨R * hi.unit⁻¹.val, ?_⟩
  rw [← Matrix.mul_assoc]
  calc
    N * R * hi.unit⁻¹.val = hi.unit.val * hi.unit⁻¹.val :=
      congrArg (fun A => A * hi.unit⁻¹.val) hi.unit_spec.symm
    _ = 1 := by rw [← Units.val_mul, mul_inv_cancel, Units.val_one]

/-- Saturate a rectangular set by right multiplication by a subgroup. -/
def adjacentRankRightSaturation
    (J : Subgroup (GeneralLinear (n + 1) K))
    (C : Set (Matrix (Fin n) (Fin (n + 1)) K)) :
    Set (Matrix (Fin n) (Fin (n + 1)) K) :=
  (fun p : Matrix (Fin n) (Fin (n + 1)) K × GeneralLinear (n + 1) K => p.1 * p.2.val) ''
    (C ×ˢ (J : Set (GeneralLinear (n + 1) K)))

omit [TopologicalSpace K] [IsTopologicalDivisionRing K] [T2Space K] in
/-- Saturation contains its original set. -/
theorem subset_adjacentRankRightSaturation
    (J : Subgroup (GeneralLinear (n + 1) K))
    (C : Set (Matrix (Fin n) (Fin (n + 1)) K)) :
    C ⊆ adjacentRankRightSaturation J C := by
  intro M hM
  exact ⟨(M, 1), ⟨hM, J.one_mem⟩, by simp⟩

omit [T2Space K] in
/-- Compact subgroups preserve compactness of saturation. -/
theorem isCompact_adjacentRankRightSaturation
    (J : Subgroup (GeneralLinear (n + 1) K))
    (hJ : IsCompact (J : Set (GeneralLinear (n + 1) K)))
    {C : Set (Matrix (Fin n) (Fin (n + 1)) K)} (hC : IsCompact C) :
    IsCompact (adjacentRankRightSaturation J C) :=
  (hC.prod hJ).image (continuous_fst.matrix_mul (Units.continuous_val.comp continuous_snd))

omit [T2Space K] in
/-- Saturation of an open rectangular set is open. -/
theorem isOpen_adjacentRankRightSaturation
    (J : Subgroup (GeneralLinear (n + 1) K))
    {C : Set (Matrix (Fin n) (Fin (n + 1)) K)} (hC : IsOpen C) :
    IsOpen (adjacentRankRightSaturation J C) := by
  have he : adjacentRankRightSaturation J C =
      ⋃ k : J, rectangularHomeomorph k.val '' C := by
    ext M
    constructor
    · rintro ⟨⟨N, k⟩, ⟨hN, hk⟩, rfl⟩
      exact mem_iUnion.mpr ⟨⟨k, hk⟩, N, hN, rfl⟩
    · intro h
      obtain ⟨k, N, hN, rfl⟩ := mem_iUnion.mp h
      exact ⟨(N, k.val), ⟨hN, k.property⟩, rfl⟩
  rw [he]
  exact isOpen_iUnion fun k => (rectangularHomeomorph k.val).isOpenMap C hC

omit [TopologicalSpace K] [IsTopologicalDivisionRing K] [T2Space K] in
/-- Full row rank is preserved by saturation. -/
theorem adjacentRankRightSaturation_fullRank
    (J : Subgroup (GeneralLinear (n + 1) K))
    {C : Set (Matrix (Fin n) (Fin (n + 1)) K)}
    (hC : C ⊆ {M | AdjacentRankFullRank M}) :
    adjacentRankRightSaturation J C ⊆ {M | AdjacentRankFullRank M} := by
  rintro _ ⟨⟨M, k⟩, ⟨hM, _⟩, rfl⟩
  exact (adjacentRankFullRank_mul_iff M k).mpr (hC hM)

omit [TopologicalSpace K] [IsTopologicalDivisionRing K] [T2Space K] in
/-- Membership in a saturated set is unchanged by right multiplication in J. -/
theorem mem_adjacentRankRightSaturation_mul_iff
    (J : Subgroup (GeneralLinear (n + 1) K))
    (C : Set (Matrix (Fin n) (Fin (n + 1)) K))
    (M : Matrix (Fin n) (Fin (n + 1)) K) (k : J) :
    M * k.val.val ∈ adjacentRankRightSaturation J C ↔
      M ∈ adjacentRankRightSaturation J C := by
  have hmul (N : Matrix (Fin n) (Fin (n + 1)) K) (j : J)
      (hN : N ∈ adjacentRankRightSaturation J C) :
      N * j.val.val ∈ adjacentRankRightSaturation J C := by
    obtain ⟨⟨A, a⟩, ⟨hA, ha⟩, rfl⟩ := hN
    exact ⟨(A, a * j.val), ⟨hA, J.mul_mem ha j.property⟩,
      by simp only [Units.val_mul, Matrix.mul_assoc]⟩
  constructor
  · intro h
    have hh := hmul (M * k.val.val) k⁻¹ h
    simpa only [InvMemClass.coe_inv, Matrix.mul_assoc, ← Units.val_mul,
      mul_inv_cancel, Units.val_one, Matrix.mul_one] using hh
  · exact hmul M k

/-- For any compact subgroup, full row rank has compact open invariant cutoffs
that eventually contain every full-rank rectangle. -/
theorem exists_adjacentRankFullRankCutoffs
    [LocallyCompactSpace K] [TotallyDisconnectedSpace K] [SecondCountableTopology K]
    (J : Subgroup (GeneralLinear (n + 1) K))
    (hJ : IsCompact (J : Set (GeneralLinear (n + 1) K))) :
    ∃ C : ℕ → Set (Matrix (Fin n) (Fin (n + 1)) K),
      (∀ m, IsCompact (C m) ∧ IsOpen (C m) ∧
        C m ⊆ {M | AdjacentRankFullRank M}) ∧
      (∀ m M (k : J), M * k.val.val ∈ C m ↔ M ∈ C m) ∧
      ∀ M, AdjacentRankFullRank M → ∀ᶠ m in atTop, M ∈ C m := by
  let : LocallyCompactSpace (Matrix (Fin n) (Fin (n + 1)) K) :=
    inferInstanceAs (LocallyCompactSpace (Fin n → Fin (n + 1) → K))
  let : TotallyDisconnectedSpace (Matrix (Fin n) (Fin (n + 1)) K) :=
    inferInstanceAs (TotallyDisconnectedSpace (Fin n → Fin (n + 1) → K))
  let : SecondCountableTopology (Matrix (Fin n) (Fin (n + 1)) K) :=
    inferInstanceAs (SecondCountableTopology (Fin n → Fin (n + 1) → K))
  obtain ⟨D, hD, _, hcover⟩ := exists_compactClopen_exhaustion_open
    (isOpen_adjacentRankFullRank (K := K) (n := n))
  refine ⟨fun m => adjacentRankRightSaturation J (D m), fun m =>
    ⟨isCompact_adjacentRankRightSaturation J hJ (hD m).1,
      isOpen_adjacentRankRightSaturation J (hD m).2.1.isOpen,
      adjacentRankRightSaturation_fullRank J (hD m).2.2⟩,
    fun m M k => mem_adjacentRankRightSaturation_mul_iff J (D m) M k, ?_⟩
  intro M hM
  filter_upwards [hcover M hM] with m hm
  exact subset_adjacentRankRightSaturation J (D m) hm

/-- Restriction of an arbitrary Schwartz test to a compact open full-rank set. -/
def adjacentRankCutoffTest
    (C : Set (Matrix (Fin n) (Fin (n + 1)) K))
    (hc : IsCompact C) (ho : IsOpen C)
    (hfull : C ⊆ {M | AdjacentRankFullRank M})
    (Φ : SchwartzBruhat (Matrix (Fin n) (Fin (n + 1)) K)) :
    adjacentRankCompactTests n K := by
  let α := compactOpenIndicator C hc ho
  let Ψ : SchwartzBruhat (Matrix (Fin n) (Fin (n + 1)) K) :=
    ⟨fun M => α M * Φ M, α.locallyConstant.comp₂ Φ.locallyConstant (· * ·),
      α.hasCompactSupport.mul_right⟩
  refine ⟨Ψ, fun M hM => hfull ?_⟩
  have hα : tsupport (α : _ → ℂ) ⊆ C :=
    closure_minimal (fun N hN => by
      by_contra h
      change C.indicator (fun _ => (1 : ℂ)) N ≠ 0 at hN
      exact hN (Set.indicator_of_notMem h _)) hc.isClosed
  exact hα (tsupport_mul_subset_left hM)

omit [IsTopologicalDivisionRing K] in
@[simp] theorem adjacentRankCutoffTest_apply
    (C : Set (Matrix (Fin n) (Fin (n + 1)) K))
    (hc : IsCompact C) (ho : IsOpen C)
    (hfull : C ⊆ {M | AdjacentRankFullRank M})
    (Φ : SchwartzBruhat (Matrix (Fin n) (Fin (n + 1)) K))
    (M : Matrix (Fin n) (Fin (n + 1)) K) :
    (adjacentRankCutoffTest C hc ho hfull Φ).val M =
      C.indicator (Φ : _ → ℂ) M := by
  classical
  change C.indicator (fun _ => (1 : ℂ)) M * Φ M = _
  by_cases h : M ∈ C <;> simp [h]

omit [IsTopologicalDivisionRing K] in
theorem norm_adjacentRankCutoffTest_le
    (C : Set (Matrix (Fin n) (Fin (n + 1)) K))
    (hc : IsCompact C) (ho : IsOpen C)
    (hfull : C ⊆ {M | AdjacentRankFullRank M})
    (Φ : SchwartzBruhat (Matrix (Fin n) (Fin (n + 1)) K))
    (M : Matrix (Fin n) (Fin (n + 1)) K) :
    ‖(adjacentRankCutoffTest C hc ho hfull Φ).val M‖ ≤ ‖Φ M‖ := by
  classical
  rw [adjacentRankCutoffTest_apply]
  by_cases hM : M ∈ C <;> simp [hM]

/-- Invariant full-rank tests approximate every Schwartz test on the full-rank
locus, with a pointwise norm bound by the original test. -/
theorem exists_adjacentRankFullRankTestApproximation
    [LocallyCompactSpace K] [TotallyDisconnectedSpace K] [SecondCountableTopology K]
    (J : Subgroup (GeneralLinear (n + 1) K))
    (hJ : IsCompact (J : Set (GeneralLinear (n + 1) K)))
    (Φ : SchwartzBruhat (Matrix (Fin n) (Fin (n + 1)) K))
    (hΦ : ∀ M (k : J), Φ (M * k.val.val) = Φ M) :
    ∃ Ψ : ℕ → adjacentRankCompactTests n K,
      (∀ m M (k : J), (Ψ m).val (M * k.val.val) = (Ψ m).val M) ∧
      (∀ m M, ‖(Ψ m).val M‖ ≤ ‖Φ M‖) ∧
      ∀ M, AdjacentRankFullRank M → ∀ᶠ m in atTop, (Ψ m).val M = Φ M := by
  classical
  obtain ⟨C, hC, hinv, hcover⟩ := exists_adjacentRankFullRankCutoffs J hJ
  let Ψ (m : ℕ) := adjacentRankCutoffTest (C m) (hC m).1
    (hC m).2.1 (hC m).2.2 Φ
  refine ⟨Ψ, ?_, fun m M => norm_adjacentRankCutoffTest_le _ _ _ _ Φ M, ?_⟩
  · intro m M k
    simp only [Ψ, adjacentRankCutoffTest_apply]
    by_cases hM : M ∈ C m
    · rw [Set.indicator_of_mem hM, Set.indicator_of_mem ((hinv m M k).mpr hM), hΦ]
    · rw [Set.indicator_of_notMem hM, Set.indicator_of_notMem
        (fun h => hM ((hinv m M k).mp h))]
  · intro M hM
    filter_upwards [hcover M hM] with m hm
    simp [Ψ, hm]

end Rectangular

end Langlands.RankinSelberg
