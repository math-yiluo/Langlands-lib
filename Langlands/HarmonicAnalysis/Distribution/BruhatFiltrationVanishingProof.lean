import Langlands.HarmonicAnalysis.Distribution.BruhatFiltrationVanishingStatement
import Langlands.HarmonicAnalysis.Distribution.OpenRestrictionLocalityProof

/-! # Finite Bruhat-filtration vanishing from actual open restrictions -/

noncomputable section

namespace Langlands.HarmonicAnalysis.Distribution.BruhatFiltrationVanishingProof

open GeneralLinear

universe u

variable (n : ℕ) (K : Type u) [Field K] [TopologicalSpace K]
  [IsTopologicalDivisionRing K] [T2Space K]
  [LocallyCompactSpace (GeneralLinear n K)]
  [TotallyDisconnectedSpace (GeneralLinear n K)]

omit [LocallyCompactSpace (GeneralLinear n K)]
  [TotallyDisconnectedSpace (GeneralLinear n K)] in
/-- Support on a closed layer gives zero restriction on its open complement. -/
theorem restrictOpen_compl_layer_zero (k : ℕ)
    (D : Distribution (GeneralLinear n K))
    (hD : D ∈ supportedOn (upperBruhatLayerLE n K k)) :
    restrictOpen (isClosed_upperBruhatLayerLE k).isOpen_compl D = 0 := by
  ext f
  apply hD
  intro g hg
  exact SchwartzBruhat.extendZero_apply_of_not_mem _ f (fun h => h hg)

/-- Vanishing on the neighborhoods of all cells at the top inversion count
removes that count from the actual support condition. -/
theorem remove_top_layer (k : ℕ) (D : Distribution (GeneralLinear n K))
    (hD : D ∈ supportedOn (upperBruhatLayerLE n K k))
    (hkill : ∀ w : Equiv.Perm (Fin n), permutationInversionCount n w = k →
      restrictOpen (isOpen_upperBruhatCellNeighborhood w) D = 0) :
    D ∈ supportedOn {g | ∃ w : Equiv.Perm (Fin n),
      permutationInversionCount n w < k ∧ g ∈ upperBruhatCell n K w} := by
  apply openRestrictionLocality
  intro g hg
  by_cases hgL : g ∈ upperBruhatLayerLE n K k
  · obtain ⟨w, hw, hgw⟩ := hgL
    have hcount : permutationInversionCount n w = k := by
      have hnlt : ¬ permutationInversionCount n w < k := fun h => hg ⟨w, h, hgw⟩
      omega
    exact ⟨upperBruhatCellNeighborhood n K w, isOpen_upperBruhatCellNeighborhood w,
      Or.inl hgw, hkill w hcount⟩
  · exact ⟨(upperBruhatLayerLE n K k)ᶜ, (isClosed_upperBruhatLayerLE k).isOpen_compl,
      hgL, restrictOpen_compl_layer_zero n K k D hD⟩

/-- If each layer-supported distribution has zero restriction to the
neighborhoods of its top cells, the original distribution is zero. -/
theorem vanishing (D : Distribution (GeneralLinear n K))
    (hkill : ∀ w : Equiv.Perm (Fin n),
      D ∈ supportedOn (upperBruhatLayerLE n K (permutationInversionCount n w)) →
        restrictOpen (isOpen_upperBruhatCellNeighborhood w) D = 0) : D = 0 := by
  have hfinite (k : ℕ) : D ∈ supportedOn (upperBruhatLayerLE n K k) → D = 0 := by
    induction k with
    | zero =>
      intro hD
      have hs := remove_top_layer n K 0 D hD (fun w hw => hkill w (hw ▸ hD))
      ext f
      apply hs
      rintro g ⟨w, hw, _⟩
      omega
    | succ k ih =>
      intro hD
      have hs := remove_top_layer n K (k + 1) D hD
        (fun w hw => hkill w (hw ▸ hD))
      apply ih
      apply supportedOn_mono (Z := {g | ∃ w : Equiv.Perm (Fin n),
        permutationInversionCount n w < k + 1 ∧ g ∈ upperBruhatCell n K w}) _ hs
      rintro g ⟨w, hw, hgw⟩
      exact ⟨w, Nat.lt_succ_iff.mp hw, hgw⟩
  apply hfinite (n * n)
  intro f hf
  have hfzero : f = 0 := by
    ext g
    obtain ⟨w, hgw⟩ := exists_mem_upperBruhatCell g
    apply hf g
    refine ⟨w, ?_, hgw⟩
    rw [permutationInversionCount_eq_card]
    simpa using (Finset.card_filter_le (Finset.univ : Finset (Fin n × Fin n))
      (fun p => p.1 < p.2 ∧ w p.2 < w p.1))
  rw [hfzero, map_zero]

end Langlands.HarmonicAnalysis.Distribution.BruhatFiltrationVanishingProof

namespace Langlands.HarmonicAnalysis.Distribution

universe u

/-- Conditional vanishing of the actual cell-neighborhood restrictions kills
an algebraic distribution by finite removal of its Bruhat support layers. -/
theorem bruhatFiltrationVanishing : BruhatFiltrationVanishingStatement.{u} := by
  intro n K _ _ _ _ _ _ D hkill
  exact BruhatFiltrationVanishingProof.vanishing n K D hkill

end Langlands.HarmonicAnalysis.Distribution
