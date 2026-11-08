import Langlands.Geometry.Building.AffineFacetSimplicialFaces

/-! # Original simplicial faces on affine torsors -/

noncomputable section

universe u v w z

namespace Langlands.Geometry.Building.AffineRootSystem

open Set AbstractBuilding

section Algebra

variable {V : Type u} {A : Type v} [AddCommGroup V] [Module ℝ V] [AddTorsor V A]
  {W : Type w} {C : Type z} [AddCommGroup W] [Module ℝ W] [AddTorsor W C]

/-- Full affine root transport identifies the original vertex types. -/
def transportedVertexEquiv (e : A ≃ᵃ[ℝ] C) (Ψ : Set (A →ᵃ[ℝ] ℝ)) :
    {a : A // IsVertex Ψ a} ≃ {c : C // IsVertex (transportedRoots e Ψ) c} where
  toFun a := ⟨e a.val, (isVertex_transportedRoots_iff e Ψ a.val).mpr a.property⟩
  invFun c := ⟨e.symm c.val, (isVertex_transportedRoots_iff e Ψ (e.symm c.val)).mp
    (by simpa only [e.apply_symm_apply] using c.property)⟩
  left_inv a := Subtype.ext (e.symm_apply_apply a.val)
  right_inv c := Subtype.ext (e.apply_symm_apply c.val)

/-- The entire vertex set of an original closed facet in an affine torsor. -/
def torsorFacetVertexSet (Ψ : Set (A →ᵃ[ℝ] ℝ)) (p : A) :
    Set {a : A // IsVertex Ψ a} :=
  {a | a.val ∈ facetClosure Ψ p}

end Algebra

section Independence

variable {V : Type u} {A : Type v}
  [NormedAddCommGroup V] [NormedSpace ℝ V] [FiniteDimensional ℝ V] [AddTorsor V A]
  {W : Type w} {C : Type z}
  [NormedAddCommGroup W] [NormedSpace ℝ W] [FiniteDimensional ℝ W] [AddTorsor W C]
  {Ψ : Set (A →ᵃ[ℝ] ℝ)}

/-- The original actual-vertex independence condition is invariant under full
affine root transport. -/
theorem affineIndependent_torsorVertexFinset_transportedRoots_iff
    (hΨ : IsAffineRootSystemWithRankZero Ψ) (e : A ≃ᵃ[ℝ] C) (p : A) :
    AffineIndependent ℝ
        ((↑) : torsorFacetClosureVertexFinset (hΨ.transport e) (e p) → C) ↔
      AffineIndependent ℝ ((↑) : torsorFacetClosureVertexFinset hΨ p → A) := by
  rw [torsorFacetClosureVertexFinset_transportedRoots]
  change AffineIndependent ℝ
      ((↑) : ((torsorFacetClosureVertexFinset hΨ p).map e.toEquiv.toEmbedding : Set C) → C) ↔ _
  rw [Finset.coe_map]
  exact e.affineIndependent_set_of_eq_iff

end Independence

section Coordinates

variable {V : Type u} {A : Type v}
  [NormedAddCommGroup V] [NormedSpace ℝ V] [FiniteDimensional ℝ V] [AddTorsor V A]
  {Ψ : Set (A →ᵃ[ℝ] ℝ)}

local instance affineTorsorSimplicialFacesDecidableEq : DecidableEq V := Classical.decEq _
local instance affineTorsorSimplicialFacesDecidableEq2 : DecidableEq A := Classical.decEq _

/-- On a vector space the torsor and vector constructions give the same
entire actual vertex finset. -/
theorem torsorFacetClosureVertexFinset_eq_vector
    {Φ : Set (V →ᵃ[ℝ] ℝ)} (hΦ : IsAffineRootSystemWithRankZero Φ) (p : V) :
    torsorFacetClosureVertexFinset hΦ p = facetClosureVertexFinset hΦ p := by
  ext x
  rw [mem_torsorFacetClosureVertexFinset, mem_facetClosureVertexFinset]

theorem affineIndependent_vectorVertexFinset_of_coordinates
    (hΨ : IsAffineRootSystemWithRankZero Ψ) (e : A ≃ᵃ[ℝ] V) (p : A)
    (hind : AffineIndependent ℝ ((↑) : torsorFacetClosureVertexFinset hΨ p → A)) :
    AffineIndependent ℝ
      ((↑) : facetClosureVertexFinset (hΨ.transport e) (e p) → V) := by
  have h := (affineIndependent_torsorVertexFinset_transportedRoots_iff hΨ e p).mpr hind
  rwa [torsorFacetClosureVertexFinset_eq_vector] at h

/-- Every nonempty subset of an independent original torsor facet's actual
vertices is exactly the vertex finset of its centroid's original facet. -/
theorem torsorFacetClosureVertexFinset_centroid_eq_of_affineIndependent
    (hΨ : IsAffineRootSystemWithRankZero Ψ) (p : A)
    (hind : AffineIndependent ℝ ((↑) : torsorFacetClosureVertexFinset hΨ p → A))
    (s : Finset A) (hs : s.Nonempty) (hsp : s ⊆ torsorFacetClosureVertexFinset hΨ p) :
    torsorFacetClosureVertexFinset hΨ (s.centroid ℝ id) = s := by
  let e : A ≃ᵃ[ℝ] V := (AffineEquiv.vaddConst ℝ (Classical.arbitrary A)).symm
  have hsub : s.map e.toEquiv.toEmbedding ⊆
      facetClosureVertexFinset (hΨ.transport e) (e p) := by
    rw [← torsorFacetClosureVertexFinset_eq_vector (hΨ.transport e) (e p),
      torsorFacetClosureVertexFinset_transportedRoots hΨ e p]
    exact Finset.map_subset_map.mpr hsp
  have hvec := facetClosureVertexFinset_centroid_eq_of_affineIndependent
    (hΨ.transport e) (e p)
    (affineIndependent_vectorVertexFinset_of_coordinates hΨ e p hind)
    (s.map e.toEquiv.toEmbedding) hs.map hsub
  apply Finset.map_injective e.toEquiv.toEmbedding
  rw [← torsorFacetClosureVertexFinset_transportedRoots,
    affineEquiv_centroid_map e s hs, torsorFacetClosureVertexFinset_eq_vector]
  exact hvec

omit [FiniteDimensional ℝ V] in
theorem preimage_torsorFacetVertexSet_coordinates
    (e : A ≃ᵃ[ℝ] V) (p : A) :
    (transportedVertexEquiv e Ψ).symm ⁻¹' torsorFacetVertexSet Ψ p =
      facetVertexSet (transportedRoots e Ψ) (e p) := by
  ext x
  change e.symm x.val ∈ facetClosure Ψ p ↔
    x.val ∈ facetClosure (transportedRoots e Ψ) (e p)
  simpa only [e.apply_symm_apply] using
    (mem_facetClosure_transportedRoots_iff e Ψ p (e.symm x.val)).symm

/-- The actual simplicial complex on the original torsor vertices. A supplied
affine coordinate equivalence is used only to construct the structure; its
faces are characterized intrinsically below. -/
def torsorFacetVertexSimplicialComplex (hΨ : IsAffineRootSystemWithRankZero Ψ)
    (hind : ∀ p : A,
      AffineIndependent ℝ ((↑) : torsorFacetClosureVertexFinset hΨ p → A))
    (e : A ≃ᵃ[ℝ] V) : SimplicialComplex {a : A // IsVertex Ψ a} :=
  (facetVertexSimplicialComplex (hΨ.transport e) (fun p =>
    by
      obtain ⟨a, rfl⟩ := e.surjective p
      exact affineIndependent_vectorVertexFinset_of_coordinates hΨ e a (hind a))).congr
        (transportedVertexEquiv e Ψ).symm

/-- The faces are exactly the entire original vertex sets, independently of
the coordinate equivalence used in the construction. -/
theorem faces_torsorFacetVertexSimplicialComplex
    (hΨ : IsAffineRootSystemWithRankZero Ψ)
    (hind : ∀ p : A,
      AffineIndependent ℝ ((↑) : torsorFacetClosureVertexFinset hΨ p → A))
    (e : A ≃ᵃ[ℝ] V) :
    (torsorFacetVertexSimplicialComplex hΨ hind e).faces =
      Set.range (torsorFacetVertexSet Ψ) := by
  ext s
  change (∃ p : V, facetVertexSet (transportedRoots e Ψ) p =
    (transportedVertexEquiv e Ψ).symm ⁻¹' s) ↔
      ∃ p : A, torsorFacetVertexSet Ψ p = s
  constructor
  · rintro ⟨p, hp⟩
    refine ⟨e.symm p, ?_⟩
    apply (Set.preimage_injective.mpr (transportedVertexEquiv e Ψ).symm.surjective)
    rw [preimage_torsorFacetVertexSet_coordinates, e.apply_symm_apply, hp]
  · rintro ⟨p, rfl⟩
    exact ⟨e p, (preimage_torsorFacetVertexSet_coordinates e p).symm⟩

theorem torsorFacetVertexSet_finite (hΨ : IsAffineRootSystemWithRankZero Ψ) (p : A) :
    (torsorFacetVertexSet Ψ p).Finite := by
  apply Set.Finite.of_finite_image (s := torsorFacetVertexSet Ψ p) (f := Subtype.val)
    ((torsorFacetClosureVertexFinset hΨ p).finite_toSet.subset ?_)
    Subtype.val_injective.injOn
  rintro _ ⟨v, hv, rfl⟩
  exact (mem_torsorFacetClosureVertexFinset hΨ p v.val).mpr ⟨hv, v.property⟩

theorem torsorFacetVertexSet_nonempty (hΨ : IsAffineRootSystemWithRankZero Ψ) (p : A) :
    (torsorFacetVertexSet Ψ p).Nonempty := by
  obtain ⟨v, hv⟩ := torsorFacetClosureVertexFinset_nonempty hΨ p
  obtain ⟨hvc, hvv⟩ := (mem_torsorFacetClosureVertexFinset hΨ p v).mp hv
  exact ⟨⟨v, hvv⟩, hvc⟩

/-- The entire original vertex sets preserve and reflect closed-facet inclusion. -/
theorem torsorFacetVertexSet_subset_iff
    (hΨ : IsAffineRootSystemWithRankZero Ψ) (p q : A) :
    torsorFacetVertexSet Ψ p ⊆ torsorFacetVertexSet Ψ q ↔
      facetClosure Ψ p ⊆ facetClosure Ψ q := by
  rw [← torsorFacetClosureVertexFinset_subset_iff hΨ p q]
  constructor
  · intro h v hv
    obtain ⟨hvc, hvv⟩ := (mem_torsorFacetClosureVertexFinset hΨ p v).mp hv
    exact (mem_torsorFacetClosureVertexFinset hΨ q v).mpr
      ⟨h (show (⟨v, hvv⟩ : {v : A // IsVertex Ψ v}) ∈
        torsorFacetVertexSet Ψ p from hvc), hvv⟩
  · intro h v hv
    exact ((mem_torsorFacetClosureVertexFinset hΨ q v.val).mp
      (h ((mem_torsorFacetClosureVertexFinset hΨ p v.val).mpr ⟨hv, v.property⟩))).1

/-- Entire original vertex sets determine the original closed facet. -/
theorem torsorFacetVertexSet_eq_iff
    (hΨ : IsAffineRootSystemWithRankZero Ψ) (p q : A) :
    torsorFacetVertexSet Ψ p = torsorFacetVertexSet Ψ q ↔
      facetClosure Ψ p = facetClosure Ψ q := by
  rw [le_antisymm_iff, le_antisymm_iff]
  exact and_congr (torsorFacetVertexSet_subset_iff hΨ p q)
    (torsorFacetVertexSet_subset_iff hΨ q p)

/-- The constructed simplices realize exactly the original closed-facet order
on the original affine torsor. -/
def torsorClosedFacetSimplicialOrderIso (hΨ : IsAffineRootSystemWithRankZero Ψ)
    (hind : ∀ p : A,
      AffineIndependent ℝ ((↑) : torsorFacetClosureVertexFinset hΨ p → A))
    (e : A ≃ᵃ[ℝ] V) :
    Set.range (facetClosure Ψ) ≃o (torsorFacetVertexSimplicialComplex hΨ hind e).faces := by
  have hmem (p : A) : torsorFacetVertexSet Ψ p ∈
      (torsorFacetVertexSimplicialComplex hΨ hind e).faces := by
    rw [faces_torsorFacetVertexSimplicialComplex]
    exact ⟨p, rfl⟩
  let f : Set.range (facetClosure Ψ) ↪o
      (torsorFacetVertexSimplicialComplex hΨ hind e).faces :=
    OrderEmbedding.ofMapLEIff
      (fun C => ⟨torsorFacetVertexSet Ψ C.property.choose, hmem C.property.choose⟩)
      (by
        intro C D
        change torsorFacetVertexSet Ψ C.property.choose ⊆
          torsorFacetVertexSet Ψ D.property.choose ↔ C.val ⊆ D.val
        rw [torsorFacetVertexSet_subset_iff hΨ,
          C.property.choose_spec, D.property.choose_spec])
  apply OrderIso.ofSurjective f
  rintro ⟨s, hs⟩
  rw [faces_torsorFacetVertexSimplicialComplex] at hs
  obtain ⟨p, rfl⟩ := hs
  refine ⟨⟨facetClosure Ψ p, ⟨p, rfl⟩⟩, ?_⟩
  apply Subtype.ext
  apply (torsorFacetVertexSet_eq_iff hΨ _ p).mpr
  exact (⟨facetClosure Ψ p, ⟨p, rfl⟩⟩ :
    Set.range (facetClosure Ψ)).property.choose_spec

/-- The original torsor simplex complex, packaged as one polysimplicial factor. -/
def torsorFacetVertexPolysimplicialComplex (hΨ : IsAffineRootSystemWithRankZero Ψ)
    (hind : ∀ p : A,
      AffineIndependent ℝ ((↑) : torsorFacetClosureVertexFinset hΨ p → A))
    (e : A ≃ᵃ[ℝ] V) :
    PolysimplicialComplex PUnit (fun _ => {a : A // IsVertex Ψ a}) :=
  ⟨fun _ => torsorFacetVertexSimplicialComplex hΨ hind e⟩

/-- One-factor polysimplicial coordinates preserve every original closed facet
and its original incidence relation. -/
def torsorClosedFacetPolysimplicialOrderIso
    (hΨ : IsAffineRootSystemWithRankZero Ψ)
    (hind : ∀ p : A,
      AffineIndependent ℝ ((↑) : torsorFacetClosureVertexFinset hΨ p → A))
    (e : A ≃ᵃ[ℝ] V) :
    Set.range (facetClosure Ψ) ≃o
      (torsorFacetVertexPolysimplicialComplex hΨ hind e).facets :=
  ((torsorClosedFacetSimplicialOrderIso hΨ hind e).trans
    (OrderIso.funUnique PUnit (torsorFacetVertexSimplicialComplex hΨ hind e).faces).symm).trans
      (torsorFacetVertexPolysimplicialComplex hΨ hind e).facetsOrderIso.symm

/-- Actual-vertex independence suffices for polysimpliciality of the original
torsor closed-facet order, including rank zero. -/
theorem isPolysimplicial_torsorClosedFacets_of_affineIndependent
    (hΨ : IsAffineRootSystemWithRankZero Ψ)
    (hind : ∀ p : A,
      AffineIndependent ℝ ((↑) : torsorFacetClosureVertexFinset hΨ p → A)) :
    IsPolysimplicial (Set.range (facetClosure Ψ)) := by
  let e : A ≃ᵃ[ℝ] V := (AffineEquiv.vaddConst ℝ (Classical.arbitrary A)).symm
  exact (torsorFacetVertexPolysimplicialComplex hΨ hind e).isPolysimplicial_facets.of_orderIso
    (torsorClosedFacetPolysimplicialOrderIso hΨ hind e).symm

end Coordinates

end Langlands.Geometry.Building.AffineRootSystem
