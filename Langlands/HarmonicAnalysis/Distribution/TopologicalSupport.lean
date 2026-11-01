import Langlands.HarmonicAnalysis.Distribution.OpenRestrictionLocalityProof

/-!
# Topological support and compactly supported algebraic distributions

Renard, 9 July 2026, II.1.2, printed p.31 / PDF p.37.
Support is defined through the actual open restrictions, then related to the
existing pointwise-annihilator submodules for closed subsets.
-/

noncomputable section

namespace Langlands.HarmonicAnalysis.Distribution

universe u

variable {X : Type u} [TopologicalSpace X] [T2Space X]

/-- The complement of the union of the open sets where the distribution
has zero open restriction. -/
def support (D : Distribution X) : Set X :=
  (⋃₀ {U : Set X | ∃ hU : IsOpen U, restrictOpen hU D = 0})ᶜ

theorem isClosed_support (D : Distribution X) : IsClosed (support D) := by
  apply IsOpen.isClosed_compl
  exact isOpen_sUnion (by rintro U ⟨hU, _⟩; exact hU)

theorem not_mem_support_iff (D : Distribution X) (x : X) :
    x ∉ support D ↔
      ∃ (U : Set X) (hU : IsOpen U), x ∈ U ∧ restrictOpen hU D = 0 := by
  change ¬ x ∈ (⋃₀ {U : Set X | ∃ hU : IsOpen U, restrictOpen hU D = 0})ᶜ ↔ _
  rw [Set.mem_compl_iff, not_not]
  constructor
  · rintro ⟨U, ⟨hU, hD⟩, hxU⟩
    exact ⟨U, hU, hxU, hD⟩
  · rintro ⟨U, hU, hxU, hD⟩
    exact ⟨U, ⟨hU, hD⟩, hxU⟩

@[simp]
theorem support_zero : support (0 : Distribution X) = ∅ := by
  apply Set.eq_empty_iff_forall_notMem.mpr
  intro x
  exact (not_mem_support_iff 0 x).mpr ⟨Set.univ, isOpen_univ, Set.mem_univ x,
    map_zero _⟩

/-- Pointwise annihilator support on a closed set forces the actual open
restriction to its complement to vanish. -/
theorem restrictOpen_compl_eq_zero {Z : Set X} (hZ : IsClosed Z)
    {D : Distribution X} (hD : D ∈ supportedOn Z) :
    restrictOpen hZ.isOpen_compl D = 0 := by
  ext f
  change D (SchwartzBruhat.extendZero hZ.isOpen_compl f) = 0
  apply hD
  intro z hz
  exact SchwartzBruhat.extendZero_apply_of_not_mem _ _ (by
    intro h
    exact h hz)

/-- This implication only needs Hausdorffness and closedness of the set. -/
theorem support_subset_of_mem_supportedOn {Z : Set X} (hZ : IsClosed Z)
    {D : Distribution X} (hD : D ∈ supportedOn Z) : support D ⊆ Z := by
  intro x hx
  by_contra hxZ
  exact ((not_mem_support_iff D x).mpr
    ⟨Zᶜ, hZ.isOpen_compl, hxZ, restrictOpen_compl_eq_zero hZ hD⟩) hx

section LocallyProfinite

variable [LocallyCompactSpace X] [TotallyDisconnectedSpace X]

/-- For closed sets, Renard's topological support condition agrees with the
existing pointwise-annihilator submodule condition. -/
theorem support_subset_iff_mem_supportedOn {Z : Set X} (hZ : IsClosed Z)
    (D : Distribution X) : support D ⊆ Z ↔ D ∈ supportedOn Z := by
  constructor
  · intro hD
    apply openRestrictionLocality X Z D
    intro x hxZ
    apply (not_mem_support_iff D x).mp
    intro hx
    exact hxZ (hD hx)
  · exact support_subset_of_mem_supportedOn hZ

theorem mem_supportedOn_support (D : Distribution X) :
    D ∈ supportedOn (support D) :=
  (support_subset_iff_mem_supportedOn (isClosed_support D) D).mp Set.Subset.rfl

theorem support_add_subset (D E : Distribution X) :
    support (D + E) ⊆ support D ∪ support E := by
  apply (support_subset_iff_mem_supportedOn
    ((isClosed_support D).union (isClosed_support E)) (D + E)).mpr
  apply (supportedOn (support D ∪ support E)).add_mem
  · exact supportedOn_mono Set.subset_union_left (mem_supportedOn_support D)
  · exact supportedOn_mono Set.subset_union_right (mem_supportedOn_support E)

theorem support_smul_subset (c : ℂ) (D : Distribution X) :
    support (c • D) ⊆ support D := by
  apply (support_subset_iff_mem_supportedOn (isClosed_support D) (c • D)).mpr
  exact (supportedOn (support D)).smul_mem c (mem_supportedOn_support D)

/-- Renard's E′(X): the actual submodule of the full algebraic dual consisting
of distributions with compact topological support. -/
def compactlySupported : Submodule ℂ (Distribution X) where
  carrier := {D | IsCompact (support D)}
  zero_mem' := by
    change IsCompact (support (0 : Distribution X))
    rw [support_zero]
    exact isCompact_empty
  add_mem' {D E} hD hE :=
    (hD.union hE).of_isClosed_subset (isClosed_support (D + E)) (support_add_subset D E)
  smul_mem' c D hD :=
    hD.of_isClosed_subset (isClosed_support (c • D)) (support_smul_subset c D)

@[simp]
theorem mem_compactlySupported_iff (D : Distribution X) :
    D ∈ compactlySupported ↔ IsCompact (support D) := Iff.rfl

/-- The compact topological support can equivalently be bounded by an actual
compact set in the existing pointwise-annihilator convention. -/
theorem mem_compactlySupported_iff_exists_compact (D : Distribution X) :
    D ∈ compactlySupported ↔
      ∃ K : Set X, IsCompact K ∧ D ∈ supportedOn K := by
  constructor
  · intro hD
    exact ⟨support D, hD, mem_supportedOn_support D⟩
  · rintro ⟨K, hK, hD⟩
    exact hK.of_isClosed_subset (isClosed_support D)
      (support_subset_of_mem_supportedOn hK.isClosed hD)

end LocallyProfinite

end Langlands.HarmonicAnalysis.Distribution
