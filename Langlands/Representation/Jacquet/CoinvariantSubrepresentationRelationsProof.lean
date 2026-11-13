import Langlands.Representation.Jacquet.CompactUnionCoinvariantStatements
import Langlands.Representation.Jacquet.ExactProof
import Langlands.Topology.LocallyProfiniteProof

/-! # Subrepresentation relations for a filtered union of compact subgroups -/

namespace Langlands.Jacquet

universe uH uV

/-- Taking relations for the top subgroup gives the usual relation submodule. -/
theorem relations_top_eq_ker {H : Type uH} [Group H]
    {E : Type uV} [AddCommGroup E] [Module ℂ E] (τ : Representation ℂ H E) :
    relations τ ⊤ = Representation.Coinvariants.ker τ := by
  apply le_antisymm
  · exact Langlands.coinvariants_ker_comp_subgroup_le τ ⊤
  · apply Submodule.span_le.mpr
    rintro _ ⟨⟨g, v⟩, rfl⟩
    exact sub_mem_relations τ ⊤ ⟨g, Subgroup.mem_top g⟩ v

/-- Finite subsets lie in compact open subgroups under the union and filtering hypotheses. -/
theorem compactOpenFiniteContainment
    (H : Type uH) [Group H] [TopologicalSpace H] [IsTopologicalGroup H]
    [T2Space H] [LocallyCompactSpace H] [TotallyDisconnectedSpace H]
    (hcover : (⋃ K : {K : Subgroup H // IsCompact (K : Set H)}, (K.1 : Set H)) =
      Set.univ)
    (hfilter : ∀ s : Finset {K : Subgroup H // IsCompact (K : Set H)},
      ∃ L : {K : Subgroup H // IsCompact (K : Set H)},
        (⋃ K ∈ s, (K.1 : Set H)) ⊆ (L.1 : Set H)) :
    ∀ s : Finset H, ∃ K : OpenSubgroup H,
      IsCompact (K : Set H) ∧ ∀ g ∈ s, g ∈ K := by
  classical
  obtain ⟨U, hU, -⟩ :=
    ((Langlands.Topology.LocallyProfiniteProof.vanDantzig H).mp
      Langlands.Topology.isLocallyProfinite_of_mathlib).2 Set.univ Filter.univ_mem
  have hpoint (g : H) :
      ∃ K : {K : Subgroup H // IsCompact (K : Set H)}, g ∈ K.1 := by
    apply Set.mem_iUnion.mp
    rw [hcover]
    trivial
  choose K hK using hpoint
  intro s
  let Uc : {K : Subgroup H // IsCompact (K : Set H)} := ⟨U.toSubgroup, hU⟩
  obtain ⟨L, hL⟩ := hfilter (insert Uc (s.image K))
  have hUL : U.toSubgroup ≤ L.1 := by
    intro g hg
    apply hL
    exact Set.mem_iUnion.mpr ⟨Uc, Set.mem_iUnion.mpr ⟨by simp, hg⟩⟩
  refine ⟨⟨L.1, Subgroup.isOpen_mono hUL U.isOpen⟩, L.2, ?_⟩
  intro g hg
  apply hL
  exact Set.mem_iUnion.mpr ⟨K g, Set.mem_iUnion.mpr
    ⟨Finset.mem_insert_of_mem (Finset.mem_image.mpr ⟨g, hg, rfl⟩), hK g⟩⟩

/-- Renard III.2.9, the first assertion of the Corollary. -/
theorem coinvariantSubrepresentationRelations :
    CoinvariantSubrepresentationRelationsStatement.{uH, uV} := by
  intro H _ _ _ _ _ _ hcover hfilter E _ _ τ hτ E'
  rw [relations_top_eq_ker, relations_top_eq_ker]
  let i : E'.toRepresentation.IntertwiningMap τ :=
    { toLinearMap := E'.toSubmodule.subtype
      isIntertwining' := fun _ => rfl }
  have hi := Langlands.coinvariants_map_injective_of_smooth
    (compactOpenFiniteContainment H hcover hfilter) i Subtype.val_injective hτ
  ext x
  constructor
  · rintro ⟨v, hv, rfl⟩
    refine ⟨?_, v.property⟩
    apply (Representation.Coinvariants.mk_eq_zero τ).mp
    change Representation.Coinvariants.mk τ (v : E) = 0
    have h := congrArg (Representation.Coinvariants.map E'.toRepresentation τ i)
      ((Representation.Coinvariants.mk_eq_zero E'.toRepresentation).mpr hv)
    change Representation.Coinvariants.mk τ (v : E) = _ at h
    simpa only [map_zero] using h
  · rintro ⟨hx, hxE⟩
    refine ⟨⟨x, hxE⟩, ?_, rfl⟩
    apply (Representation.Coinvariants.mk_eq_zero E'.toRepresentation).mp
    apply hi
    change Representation.Coinvariants.mk τ x = _
    simpa only [map_zero] using (Representation.Coinvariants.mk_eq_zero τ).mpr hx

end Langlands.Jacquet
