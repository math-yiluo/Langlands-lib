import Langlands.Representation.Aubert.General.RationalInductionStagesGeometry
import Langlands.Representation.Aubert.General.RationalIwasawaCartan

/-! # Compact coset representatives in a semidirect Levi subgroup -/

noncomputable section

universe u

namespace Langlands.Aubert.General.IsSemidirectDecomposition

variable {G : Type u} [Group G] [TopologicalSpace G]
  {P M U Q : Subgroup G}

/-- Intersect ambient representatives with the parabolic, then project them
to its actual Levi subgroup. -/
def leviCosetRepresentatives (h : IsSemidirectDecomposition P M U)
    (C : Set G) : Set M :=
  h.projection '' ((fun p : P => (p : G)) ⁻¹' C)

/-- Closedness of the parabolic and continuity of the projection preserve
compactness of the constructed representatives. -/
theorem isCompact_leviCosetRepresentatives
    (h : IsSemidirectDecomposition P M U)
    (hP : IsClosed (P : Set G)) (hproj : Continuous h.projection)
    {C : Set G} (hC : IsCompact C) :
    IsCompact (h.leviCosetRepresentatives C) :=
  (hP.isClosedEmbedding_subtypeVal.isCompact_preimage hC).image hproj

omit [TopologicalSpace G] in
/-- If `U ≤ Q ≤ P`, the projected representatives meet every right coset of
`Q ∩ M` in `M`. -/
theorem leviCosetRepresentatives_cover
    (h : IsSemidirectDecomposition P M U)
    (hQP : Q ≤ P) (hUQ : U ≤ Q) {C : Set G}
    (hcover : ∀ g : G, ∃ q ∈ Q, ∃ c ∈ C, g = q * c) :
    ∀ m : M, ∃ q ∈ Q.subgroupOf M,
      ∃ c ∈ h.leviCosetRepresentatives C, m = q * c := by
  intro m
  obtain ⟨q, hq, c, hc, heq⟩ := hcover m
  have hcP : c ∈ P := by
    have heq' : c = q⁻¹ * (m : G) := by
      rw [heq, inv_mul_cancel_left]
    rw [heq']
    exact P.mul_mem (P.inv_mem (hQP hq)) (h.levi_le m.property)
  let qp : P := ⟨q, hQP hq⟩
  let cp : P := ⟨c, hcP⟩
  refine ⟨h.projection qp,
    h.projection_mem_of_radical_le hQP hUQ ⟨q, hq⟩,
    h.projection cp, ⟨cp, hc, rfl⟩, ?_⟩
  have hp : (⟨m, h.levi_le m.property⟩ : P) = qp * cp :=
    Subtype.ext heq
  calc
    m = h.projection ⟨m, h.levi_le m.property⟩ := (h.projection_levi m).symm
    _ = h.projection qp * h.projection cp := by rw [hp, map_mul]

/-- A compact coset cover in the ambient group gives a compact coset cover
inside the Levi, for every subgroup containing the radical. -/
theorem hasCompactCosetCover_subgroupOf_levi
    (h : IsSemidirectDecomposition P M U)
    (hP : IsClosed (P : Set G)) (hproj : Continuous h.projection)
    (hQP : Q ≤ P) (hUQ : U ≤ Q)
    (hQ : Induction.HasCompactCosetCover Q) :
    Induction.HasCompactCosetCover (Q.subgroupOf M) := by
  obtain ⟨C, hC, hcover⟩ := hQ
  exact ⟨h.leviCosetRepresentatives C,
    h.isCompact_leviCosetRepresentatives hP hproj hC,
    h.leviCosetRepresentatives_cover hQP hUQ hcover⟩

/-- Compactness of the ambient quotient implies compactness of the literal
quotient inside the Levi. -/
theorem compactSpace_leftQuotient_subgroupOf_levi
    [IsTopologicalGroup G] [WeaklyLocallyCompactSpace G]
    (h : IsSemidirectDecomposition P M U)
    (hP : IsClosed (P : Set G)) (hproj : Continuous h.projection)
    (hQP : Q ≤ P) (hUQ : U ≤ Q)
    [CompactSpace (Induction.LeftQuotient Q)] :
    CompactSpace (Induction.LeftQuotient (Q.subgroupOf M)) :=
  Induction.compactSpace_of_hasCompactCosetCover
    (h.hasCompactCosetCover_subgroupOf_levi hP hproj hQP hUQ
      (Induction.hasCompactCosetCover_of_compactSpace Q))

end Langlands.Aubert.General.IsSemidirectDecomposition
