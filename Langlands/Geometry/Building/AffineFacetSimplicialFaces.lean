import Langlands.Geometry.Building.AffineFacetCentroids
import Langlands.Geometry.Building.AbstractBuilding
import Mathlib.LinearAlgebra.AffineSpace.Basis

/-! # Simplicial faces from affinely independent actual facet vertices -/

noncomputable section

universe u v

namespace Langlands.Geometry.Building.AffineRootSystem

open Set GalleryGeometry

section SupportingFunctionals

variable {V : Type u} {A : Type v}
  [AddCommGroup V] [Module ℝ V] [AddTorsor V A]
  {Ψ : Set (A →ᵃ[ℝ] ℝ)}

/-- A nonnegative affine functional on an original closed facet, vanishing at
one point, vanishes on that point's entire original closed facet. -/
theorem affineMap_eq_zero_on_facetClosure
    (hΨ : IsLocallyFiniteReflectionArrangement Ψ) {p x : A}
    (hx : x ∈ facetClosure Ψ p) (f : A →ᵃ[ℝ] ℝ)
    (hf : ∀ y ∈ facetClosure Ψ p, 0 ≤ f y) (hfx : f x = 0)
    {y : A} (hy : y ∈ facetClosure Ψ x) : f y = 0 := by
  obtain ⟨ε, hε, hsign⟩ :=
    exists_pos_of_eventually (eventually_sign_smul_vadd hΨ x (x -ᵥ y))
  have hz : ε • (x -ᵥ y) +ᵥ x ∈ facet Ψ x := by
    intro ψ hψ
    by_cases hzero : ψ x = 0
    · have hzero' : ψ y = 0 := by
        apply sign_eq_zero_iff.mp
        simpa only [hzero, sign_zero, or_self] using hy ψ hψ
      have hd : ψ.linear (x -ᵥ y) = 0 := by
        rw [ψ.linearMap_vsub, hzero, hzero', vsub_eq_sub, sub_self]
      rw [apply_smul_vadd, hd, hzero]
      simp
    · exact (hsign ψ hψ hzero).symm
  have hnonneg := hf _ ((facet_subset_facetClosure_iff.mpr hx) hz)
  rw [AffineMap.map_vadd, map_smul, f.linearMap_vsub, hfx,
    vsub_eq_sub, zero_sub, smul_eq_mul, vadd_eq_add, add_zero] at hnonneg
  have hfy : 0 ≤ f y := hf y (mem_facetClosure_trans hx hy)
  have hn : f y ≤ 0 := by nlinarith
  exact le_antisymm hn hfy

end SupportingFunctionals

section SimplicialFaces

variable {V : Type u} [NormedAddCommGroup V] [NormedSpace ℝ V]
  [FiniteDimensional ℝ V] {Ψ : Set (V →ᵃ[ℝ] ℝ)}

local instance : DecidableEq V := Classical.decEq _

/-- Every nonempty subset of the actual vertices of a simplex-shaped original
closed facet is exactly the actual vertex set of its centroid's original facet. -/
theorem facetClosureVertexFinset_centroid_eq_of_affineIndependent
    (hΨ : IsAffineRootSystemWithRankZero Ψ) (p : V)
    (hind : AffineIndependent ℝ
      ((↑) : facetClosureVertexFinset hΨ p → V))
    (s : Finset V) (hs : s.Nonempty) (hsp : s ⊆ facetClosureVertexFinset hΨ p) :
    facetClosureVertexFinset hΨ (s.centroid ℝ id) = s := by
  have hsmem : ∀ y ∈ s, y ∈ facetClosure Ψ p :=
    fun y hy => ((mem_facetClosureVertexFinset hΨ p y).mp (hsp hy)).1
  have hcp : s.centroid ℝ id ∈ facetClosure Ψ p :=
    centroid_mem_facetClosure s hs hsmem
  apply Finset.Subset.antisymm
  · intro v hv
    obtain ⟨hvc, hvvert⟩ := (mem_facetClosureVertexFinset hΨ _ v).mp hv
    have hvp : v ∈ facetClosureVertexFinset hΨ p :=
      (mem_facetClosureVertexFinset hΨ p v).mpr
        ⟨mem_facetClosure_trans hcp hvc, hvvert⟩
    by_contra hvs
    obtain ⟨T, hUT, hTind, hTspan⟩ :=
      exists_subset_affineIndependent_affineSpan_eq_top hind
    let b : AffineBasis T ℝ V :=
      ⟨Subtype.val, hTind, by simpa only [Subtype.range_coe_subtype, Set.ofPred_mem_eq] using hTspan⟩
    let f := b.coord ⟨v, hUT hvp⟩
    have hfw (w : V) (hw : w ∈ facetClosureVertexFinset hΨ p) :
        f w = if v = w then 1 else 0 := by
      change b.coord ⟨v, hUT hvp⟩ (b ⟨w, hUT hw⟩) = _
      rw [b.coord_apply]
      simp only [Subtype.mk.injEq]
    have hfn : ∀ w ∈ facetClosure Ψ p, 0 ≤ f w := by
      have hbase : (↑(facetClosureVertexFinset hΨ p) : Set V) ⊆ {w | 0 ≤ f w} := by
        intro w hw
        change 0 ≤ f w
        rw [hfw w hw]
        split_ifs <;> norm_num
      have hconv : Convex ℝ {w | 0 ≤ f w} := (convex_Ici (0 : ℝ)).affine_preimage f
      have h := convexHull_min hbase hconv
      rw [convexHull_facetClosureVertexFinset hΨ p] at h
      exact fun w hw => h hw
    have hfc : f (s.centroid ℝ id) = 0 := by
      rw [affineMap_centroid_eq_average s hs f]
      have hfs : ∀ w ∈ s, f w = 0 := by
        intro w hw
        rw [hfw w (hsp hw), ite_eq_right]
        rintro rfl
        exact hvs hw
      rw [Finset.sum_eq_zero hfs, mul_zero]
    have hfv := affineMap_eq_zero_on_facetClosure hΨ.isLocallyFiniteReflectionArrangement
      hcp f hfn hfc hvc
    rw [hfw v hvp, ite_eq_left rfl] at hfv
    exact one_ne_zero hfv
  · intro v hv
    exact (mem_facetClosureVertexFinset hΨ _ v).mpr
      ⟨mem_facetClosure_centroid s hs hsmem v hv,
        ((mem_facetClosureVertexFinset hΨ p v).mp (hsp hv)).2⟩

end SimplicialFaces

section Complex

variable {V : Type u} [NormedAddCommGroup V] [NormedSpace ℝ V]
  [FiniteDimensional ℝ V] {Ψ : Set (V →ᵃ[ℝ] ℝ)}

local instance : DecidableEq V := Classical.decEq _

/-- The entire actual vertex set of an original closed facet, viewed on the
type of original vertices. -/
def facetVertexSet (Ψ : Set (V →ᵃ[ℝ] ℝ)) (p : V) :
    Set {v : V // IsVertex Ψ v} :=
  {v | v.val ∈ facetClosure Ψ p}

theorem facetVertexSet_finite (hΨ : IsAffineRootSystemWithRankZero Ψ) (p : V) :
    (facetVertexSet Ψ p).Finite := by
  apply Set.Finite.of_finite_image (s := facetVertexSet Ψ p) (f := Subtype.val)
    ((facetClosureVertexFinset hΨ p).finite_toSet.subset ?_)
    Subtype.val_injective.injOn
  rintro _ ⟨v, hv, rfl⟩
  exact (mem_facetClosureVertexFinset hΨ p v.val).mpr ⟨hv, v.property⟩

theorem facetVertexSet_nonempty (hΨ : IsAffineRootSystemWithRankZero Ψ) (p : V) :
    (facetVertexSet Ψ p).Nonempty := by
  obtain ⟨v, hv⟩ := facetClosureVertexFinset_nonempty hΨ p
  obtain ⟨hvc, hvv⟩ := (mem_facetClosureVertexFinset hΨ p v).mp hv
  exact ⟨⟨v, hvv⟩, hvc⟩

/-- The exact original vertex sets preserve and reflect original closed-facet
inclusion. -/
theorem facetVertexSet_subset_iff (hΨ : IsAffineRootSystemWithRankZero Ψ) (p q : V) :
    facetVertexSet Ψ p ⊆ facetVertexSet Ψ q ↔
      facetClosure Ψ p ⊆ facetClosure Ψ q := by
  rw [← facetClosureVertexFinset_subset_iff hΨ p q]
  constructor
  · intro h v hv
    obtain ⟨hvc, hvv⟩ := (mem_facetClosureVertexFinset hΨ p v).mp hv
    exact (mem_facetClosureVertexFinset hΨ q v).mpr
      ⟨h (show (⟨v, hvv⟩ : {v : V // IsVertex Ψ v}) ∈ facetVertexSet Ψ p from hvc), hvv⟩
  · intro h v hv
    exact ((mem_facetClosureVertexFinset hΨ q v.val).mp
      (h ((mem_facetClosureVertexFinset hΨ p v.val).mpr ⟨hv, v.property⟩))).1

/-- Equality of entire actual vertex sets is equality of original closed facets. -/
theorem facetVertexSet_eq_iff (hΨ : IsAffineRootSystemWithRankZero Ψ) (p q : V) :
    facetVertexSet Ψ p = facetVertexSet Ψ q ↔
      facetClosure Ψ p = facetClosure Ψ q := by
  rw [le_antisymm_iff, le_antisymm_iff]
  exact and_congr (facetVertexSet_subset_iff hΨ p q) (facetVertexSet_subset_iff hΨ q p)

/-- Original affine face incidence is inclusion of the entire actual vertex sets. -/
theorem isFaceOf_facet_iff_facetVertexSet_subset
    (hΨ : IsAffineRootSystemWithRankZero Ψ) (p q : V) :
    IsFaceOf Ψ (facet Ψ p) (facet Ψ q) ↔
      facetVertexSet Ψ p ⊆ facetVertexSet Ψ q :=
  isFaceOf_facet_iff_facetClosure_subset.trans (facetVertexSet_subset_iff hΨ p q).symm

/-- Every nonempty subset of the vertices of an independent original closed
facet is the entire actual vertex set of another original closed facet. -/
theorem exists_facetVertexSet_eq_of_nonempty_subset
    (hΨ : IsAffineRootSystemWithRankZero Ψ) (p : V)
    (hind : AffineIndependent ℝ ((↑) : facetClosureVertexFinset hΨ p → V))
    {s : Set {v : V // IsVertex Ψ v}} (hs : s.Nonempty)
    (hsp : s ⊆ facetVertexSet Ψ p) :
    ∃ q : V, facetVertexSet Ψ q = s := by
  classical
  have hfinite : s.Finite := (facetVertexSet_finite hΨ p).subset hsp
  let t : Finset V := hfinite.toFinset.map ⟨Subtype.val, Subtype.val_injective⟩
  have htmem (v : V) : v ∈ t ↔ ∃ x ∈ s, x.val = v := by
    simp only [t, Finset.mem_map, Set.Finite.mem_toFinset, Function.Embedding.coeFn_mk]
  have htne : t.Nonempty := by
    obtain ⟨x, hx⟩ := hs
    exact ⟨x.val, (htmem x.val).mpr ⟨x, hx, rfl⟩⟩
  have htsub : t ⊆ facetClosureVertexFinset hΨ p := by
    intro v hv
    obtain ⟨x, hx, rfl⟩ := (htmem v).mp hv
    exact (mem_facetClosureVertexFinset hΨ p x.val).mpr ⟨hsp hx, x.property⟩
  have hq := facetClosureVertexFinset_centroid_eq_of_affineIndependent
    hΨ p hind t htne htsub
  refine ⟨t.centroid ℝ id, ?_⟩
  ext x
  have hx : x.val ∈ facetClosure Ψ (t.centroid ℝ id) ↔
      x.val ∈ facetClosureVertexFinset hΨ (t.centroid ℝ id) := by
    simp only [mem_facetClosureVertexFinset, x.property, and_true]
  change x.val ∈ facetClosure Ψ (t.centroid ℝ id) ↔ x ∈ s
  rw [hx, hq, htmem]
  constructor
  · rintro ⟨y, hy, he⟩
    exact (Subtype.ext he : y = x) ▸ hy
  · exact fun hx => ⟨x, hx, rfl⟩

open AbstractBuilding

/-- The simplicial complex whose faces are precisely the entire vertex sets
of original closed facets. Independence is required of every original facet. -/
def facetVertexSimplicialComplex (hΨ : IsAffineRootSystemWithRankZero Ψ)
    (hind : ∀ p : V,
      AffineIndependent ℝ ((↑) : facetClosureVertexFinset hΨ p → V)) :
    SimplicialComplex {v : V // IsVertex Ψ v} where
  faces := Set.range (facetVertexSet Ψ)
  nonempty_vertices := by
    obtain ⟨v, _⟩ := facetVertexSet_nonempty hΨ (0 : V)
    exact ⟨v⟩
  finite_of_mem s hs := by
    obtain ⟨p, rfl⟩ := hs
    exact facetVertexSet_finite hΨ p
  nonempty_of_mem s hs := by
    obtain ⟨p, rfl⟩ := hs
    exact facetVertexSet_nonempty hΨ p
  singleton_mem v := by
    exact exists_facetVertexSet_eq_of_nonempty_subset hΨ v.val (hind v.val)
      (Set.singleton_nonempty v)
      (Set.singleton_subset_iff.mpr (mem_facetClosure_self Ψ v.val))
  mem_of_subset s hs t ht hts := by
    obtain ⟨p, rfl⟩ := hs
    exact exists_facetVertexSet_eq_of_nonempty_subset hΨ p (hind p) ht hts

/-- Original closed facets, with their original incidence order, are exactly
the simplices of the constructed complex. -/
def closedFacetSimplicialOrderIso (hΨ : IsAffineRootSystemWithRankZero Ψ)
    (hind : ∀ p : V,
      AffineIndependent ℝ ((↑) : facetClosureVertexFinset hΨ p → V)) :
    Set.range (facetClosure Ψ) ≃o (facetVertexSimplicialComplex hΨ hind).faces := by
  let e : Set.range (facetClosure Ψ) ↪o (facetVertexSimplicialComplex hΨ hind).faces :=
    OrderEmbedding.ofMapLEIff
      (fun C => ⟨facetVertexSet Ψ C.property.choose, ⟨C.property.choose, rfl⟩⟩)
      (by
        intro C D
        change facetVertexSet Ψ C.property.choose ⊆ facetVertexSet Ψ D.property.choose ↔
          C.val ⊆ D.val
        rw [facetVertexSet_subset_iff hΨ, C.property.choose_spec, D.property.choose_spec])
  apply OrderIso.ofSurjective e
  rintro ⟨s, hs⟩
  obtain ⟨p, rfl⟩ := hs
  refine ⟨⟨facetClosure Ψ p, ⟨p, rfl⟩⟩, ?_⟩
  apply Subtype.ext
  apply (facetVertexSet_eq_iff hΨ _ p).mpr
  exact (⟨facetClosure Ψ p, ⟨p, rfl⟩⟩ :
    Set.range (facetClosure Ψ)).property.choose_spec

/-- The actual simplex complex as a one-factor polysimplicial complex. -/
def facetVertexPolysimplicialComplex (hΨ : IsAffineRootSystemWithRankZero Ψ)
    (hind : ∀ p : V,
      AffineIndependent ℝ ((↑) : facetClosureVertexFinset hΨ p → V)) :
    PolysimplicialComplex PUnit (fun _ => {v : V // IsVertex Ψ v}) :=
  ⟨fun _ => facetVertexSimplicialComplex hΨ hind⟩

/-- The constructed one-factor complex realizes the original closed-facet
order, without adding or subdividing facets. -/
def closedFacetPolysimplicialOrderIso (hΨ : IsAffineRootSystemWithRankZero Ψ)
    (hind : ∀ p : V,
      AffineIndependent ℝ ((↑) : facetClosureVertexFinset hΨ p → V)) :
    Set.range (facetClosure Ψ) ≃o (facetVertexPolysimplicialComplex hΨ hind).facets :=
  ((closedFacetSimplicialOrderIso hΨ hind).trans
    (OrderIso.funUnique PUnit (facetVertexSimplicialComplex hΨ hind).faces).symm).trans
      (facetVertexPolysimplicialComplex hΨ hind).facetsOrderIso.symm

/-- Affine independence of every original facet's actual vertices suffices for
polysimpliciality of the original closed-facet order. -/
theorem isPolysimplicial_closedFacets_of_affineIndependent
    (hΨ : IsAffineRootSystemWithRankZero Ψ)
    (hind : ∀ p : V,
      AffineIndependent ℝ ((↑) : facetClosureVertexFinset hΨ p → V)) :
    IsPolysimplicial (Set.range (facetClosure Ψ)) :=
  (facetVertexPolysimplicialComplex hΨ hind).isPolysimplicial_facets.of_orderIso
    (closedFacetPolysimplicialOrderIso hΨ hind).symm

end Complex

end Langlands.Geometry.Building.AffineRootSystem
