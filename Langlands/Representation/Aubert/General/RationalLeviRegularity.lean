import Langlands.Representation.Aubert.General.Parabolic

noncomputable section

namespace Langlands.Aubert.General.IsSemidirectDecomposition

universe u

variable {G : Type u} [Group G] [TopologicalSpace G] [T2Space G]
  {P M U : Subgroup G}

/-- A continuous Levi projection makes its image closed in a closed parabolic. -/
theorem isClosed_levi_of_continuous_projection (h : IsSemidirectDecomposition P M U)
    (hP : IsClosed (P : Set G)) (hπ : Continuous h.projection) :
    IsClosed (M : Set G) := by
  have hfix : IsClosed {p : P | (h.projection p : G) = (p : G)} :=
    isClosed_eq (continuous_subtype_val.comp hπ) continuous_subtype_val
  have himage : (fun p : P => (p : G)) ''
      {p : P | (h.projection p : G) = (p : G)} = (M : Set G) := by
    ext g
    constructor
    · rintro ⟨p, hp, rfl⟩
      change (h.projection p : G) = (p : G) at hp
      change (p : G) ∈ M
      exact hp ▸ (h.projection p).property
    · intro hg
      refine ⟨⟨g, h.levi_le hg⟩, ?_, rfl⟩
      exact congrArg Subtype.val (h.projection_levi ⟨g, hg⟩)
  rw [← himage]
  exact hP.isClosedEmbedding_subtypeVal.isClosedMap _ hfix

end Langlands.Aubert.General.IsSemidirectDecomposition
