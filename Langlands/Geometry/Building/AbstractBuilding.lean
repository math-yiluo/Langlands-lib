import Mathlib.Data.Fintype.Pi
import Mathlib.Data.Set.Card
import Mathlib.Logic.Equiv.Basic
import Mathlib.Logic.Equiv.Set
import Mathlib.Logic.Relation
import Mathlib.Order.Hom.Basic
import Mathlib.Order.Minimal

/-!
# Kaletha–Prasad abstract buildings: polysimplicial complexes, chamber complexes, buildings

The combinatorial notions of Kaletha–Prasad §1.5: simplicial and polysimplicial complexes
(Definition 1.5.1), their facets, faces, codimension-one faces, subcomplexes, chamber
complexes, galleries, thick and thin chamber complexes and isomorphisms, and buildings
(Definition 1.5.5, axioms BL 1–BL 4).

A polysimplicial complex `(B₁, …, Bₙ)` has vertex set `V₁ × ⋯ × Vₙ` and facets the products
`A₁ × ⋯ × Aₙ` of simplices; the facets are subsets of the product vertex set, so faces,
intersections and chambers are taken literally as in the source. The notions for chamber
complexes are stated for an arbitrary set of facets, so that they also apply to subcomplexes
such as apartments. Such a set is a polysimplicial complex when it is order-isomorphic to the
facets of one (`IsPolysimplicial`, KP Remark 1.5.4), and a chamber complex must be one. Gallery
steps use the meet of two facets in the ordered set, which on subcomplexes of polysimplicial
complexes is their intersection, so all chamber-complex notions are invariant under order
isomorphisms.

No group, field, apartment of a reductive group, Tits system or geometric realization is
involved.
-/

namespace Langlands.Geometry.Building.AbstractBuilding

universe u v w

/-! ### Simplicial and polysimplicial complexes -/

/-- A simplicial complex `(V, B)` (KP Definition 1.5.1(1)): a non-empty vertex set `V` and a
set `B` of non-empty finite subsets of `V` (the simplices) containing every singleton and
every non-empty subset of each of its members. -/
structure SimplicialComplex (V : Type u) where
  faces : Set (Set V)
  nonempty_vertices : Nonempty V
  finite_of_mem : ∀ s ∈ faces, s.Finite
  nonempty_of_mem : ∀ s ∈ faces, s.Nonempty
  singleton_mem : ∀ x : V, ({x} : Set V) ∈ faces
  mem_of_subset : ∀ s ∈ faces, ∀ t : Set V, t.Nonempty → t ⊆ s → t ∈ faces

theorem SimplicialComplex.faces_nonempty {V : Type u} (K : SimplicialComplex V) :
    K.faces.Nonempty :=
  let ⟨x⟩ := K.nonempty_vertices
  ⟨{x}, K.singleton_mem x⟩

/-- Transport of a simplicial complex along a bijection `f` of vertex sets: the simplices are the
sets whose preimage under `f` is a simplex. -/
def SimplicialComplex.congr {V : Type u} {W : Type w} (K : SimplicialComplex V) (f : V ≃ W) :
    SimplicialComplex W where
  faces := {t | f ⁻¹' t ∈ K.faces}
  nonempty_vertices := K.nonempty_vertices.map f
  finite_of_mem t ht := (K.finite_of_mem (f ⁻¹' t) ht).of_preimage f.surjective
  nonempty_of_mem t ht :=
    let ⟨x, hx⟩ := K.nonempty_of_mem (f ⁻¹' t) ht
    ⟨f x, hx⟩
  singleton_mem y := by
    have h : f ⁻¹' {y} = {f.symm y} := by
      ext x
      simp [Equiv.eq_symm_apply]
    show f ⁻¹' {y} ∈ K.faces
    rw [h]
    exact K.singleton_mem _
  mem_of_subset s hs t ht hts :=
    K.mem_of_subset (f ⁻¹' s) hs (f ⁻¹' t)
      (let ⟨y, hy⟩ := ht
       ⟨f.symm y, by simpa using hy⟩)
      (Set.preimage_mono hts)

/-- The simplices of `K` and of its transport along `f`, ordered by inclusion, are
order-isomorphic via `s ↦ f '' s`. -/
def SimplicialComplex.congrFacesOrderIso {V : Type u} {W : Type w} (K : SimplicialComplex V)
    (f : V ≃ W) : K.faces ≃o (K.congr f).faces where
  toFun s := ⟨f.symm ⁻¹' (s : Set V),
    show f ⁻¹' (f.symm ⁻¹' (s : Set V)) ∈ K.faces by rw [f.preimage_symm_preimage]; exact s.2⟩
  invFun t := ⟨f ⁻¹' (t : Set W), t.2⟩
  left_inv s := Subtype.ext (f.preimage_symm_preimage s)
  right_inv t := Subtype.ext (f.symm_preimage_preimage t)
  map_rel_iff' := f.symm.preimage_subset _ _

/-- A polysimplicial complex (KP Definition 1.5.1(2)): a finite family `(Bᵢ)ᵢ` of simplicial
complexes. Its vertex set is `∀ i, V i` and its facets are the products of simplices
(`PolysimplicialComplex.facets`). -/
structure PolysimplicialComplex (ι : Type v) [Finite ι] (V : ι → Type u) where
  factor : ∀ i, SimplicialComplex (V i)

namespace PolysimplicialComplex

variable {ι : Type v} [Finite ι] {V : ι → Type u}

/-- The facets `A₁ × ⋯ × Aₙ ⊆ V₁ × ⋯ × Vₙ` with `Aᵢ ∈ Bᵢ` (KP Definition 1.5.1(2),(3)). -/
def facets (K : PolysimplicialComplex ι V) : Set (Set (∀ i, V i)) :=
  {F | ∃ s : ∀ i, Set (V i), (∀ i, s i ∈ (K.factor i).faces) ∧ F = Set.univ.pi s}

theorem mem_facets {K : PolysimplicialComplex ι V} {F : Set (∀ i, V i)} :
    F ∈ K.facets ↔ ∃ s : ∀ i, Set (V i), (∀ i, s i ∈ (K.factor i).faces) ∧ F = Set.univ.pi s :=
  Iff.rfl

theorem pi_mem_facets (K : PolysimplicialComplex ι V) {s : ∀ i, Set (V i)}
    (hs : ∀ i, s i ∈ (K.factor i).faces) : Set.univ.pi s ∈ K.facets :=
  ⟨s, hs, rfl⟩

/-- Every vertex is a facet. -/
theorem singleton_mem_facets (K : PolysimplicialComplex ι V) (x : ∀ i, V i) :
    ({x} : Set (∀ i, V i)) ∈ K.facets :=
  ⟨fun i => {x i}, fun i => (K.factor i).singleton_mem (x i), (Set.univ_pi_singleton x).symm⟩

theorem nonempty_of_mem_facets {K : PolysimplicialComplex ι V} {F : Set (∀ i, V i)}
    (hF : F ∈ K.facets) : F.Nonempty := by
  obtain ⟨s, hs, rfl⟩ := hF
  exact Set.univ_pi_nonempty_iff.2 fun i => (K.factor i).nonempty_of_mem _ (hs i)

theorem finite_of_mem_facets {K : PolysimplicialComplex ι V} {F : Set (∀ i, V i)}
    (hF : F ∈ K.facets) : F.Finite := by
  obtain ⟨s, hs, rfl⟩ := hF
  exact Set.Finite.pi fun i => (K.factor i).finite_of_mem _ (hs i)

/-- A non-empty intersection of two facets is a facet: `∏ᵢ sᵢ ∩ ∏ᵢ tᵢ = ∏ᵢ (sᵢ ∩ tᵢ)`. -/
theorem inter_mem_facets {K : PolysimplicialComplex ι V} {F G : Set (∀ i, V i)}
    (hF : F ∈ K.facets) (hG : G ∈ K.facets) (hFG : (F ∩ G).Nonempty) : F ∩ G ∈ K.facets := by
  obtain ⟨s, hs, rfl⟩ := hF
  obtain ⟨t, ht, rfl⟩ := hG
  rw [← Set.pi_inter_distrib] at hFG ⊢
  exact K.pi_mem_facets fun i => (K.factor i).mem_of_subset _ (hs i) _
    (Set.univ_pi_nonempty_iff.1 hFG i) Set.inter_subset_left

/-- For facets, inclusion of products is inclusion of the factors. -/
theorem pi_subset_pi_iff {K : PolysimplicialComplex ι V} {s t : ∀ i, Set (V i)}
    (hs : ∀ i, s i ∈ (K.factor i).faces) :
    Set.univ.pi s ⊆ Set.univ.pi t ↔ ∀ i, s i ⊆ t i := by
  rw [Set.pi_subset_pi_iff]
  refine ⟨fun h => h.elim (fun h i => h i (Set.mem_univ i)) fun h => ?_,
    fun h => Or.inl fun i _ => h i⟩
  exact absurd h (nonempty_of_mem_facets (K.pi_mem_facets hs)).ne_empty

/-- The facets of `K`, ordered by inclusion, are the tuples of simplices with the product order,
KP's `B = B₁ × ⋯ × Bₙ` (Definition 1.5.1(2)): `F ↦ (i ↦ prᵢ F)`, with inverse
`(sᵢ)ᵢ ↦ ∏ᵢ sᵢ`. -/
def facetsOrderIso (K : PolysimplicialComplex ι V) : K.facets ≃o ∀ i, (K.factor i).faces where
  toFun F i := ⟨(fun x => x i) '' (F : Set (∀ i, V i)), by
    obtain ⟨s, hs, hF⟩ := F.2
    rw [hF, Set.eval_image_univ_pi (nonempty_of_mem_facets (K.pi_mem_facets hs))]
    exact hs i⟩
  invFun s := ⟨Set.univ.pi fun i => (s i : Set (V i)), K.pi_mem_facets fun i => (s i).2⟩
  left_inv F := by
    obtain ⟨F, s, hs, rfl⟩ := F
    refine Subtype.ext (congrArg (Set.univ.pi) (funext fun i => ?_))
    exact Set.eval_image_univ_pi (nonempty_of_mem_facets (K.pi_mem_facets hs))
  right_inv s := funext fun i => Subtype.ext <|
    Set.eval_image_univ_pi (nonempty_of_mem_facets (K.pi_mem_facets fun i => (s i).2))
  map_rel_iff' {F G} := by
    obtain ⟨F, s, hs, rfl⟩ := F
    obtain ⟨G, t, ht, rfl⟩ := G
    have hsn := nonempty_of_mem_facets (K.pi_mem_facets hs)
    have htn := nonempty_of_mem_facets (K.pi_mem_facets ht)
    change (∀ i, (fun x => x i) '' Set.univ.pi s ⊆ (fun x => x i) '' Set.univ.pi t) ↔
      Set.univ.pi s ⊆ Set.univ.pi t
    simp only [Set.eval_image_univ_pi hsn, Set.eval_image_univ_pi htn]
    exact (pi_subset_pi_iff hs).symm

end PolysimplicialComplex

/-! ### Faces, subcomplexes and chamber complexes

These notions are stated for an arbitrary set `B` of facets, ordered by inclusion. -/

section ChamberComplex

variable {X : Type u}

/-- `codim(A, C) = 1` (KP Definition 1.5.1(5)): `A ⊊ C` are facets of `B` and no facet of `B`
lies strictly between them. -/
def IsCodimOneFace (B : Set (Set X)) (A C : Set X) : Prop :=
  A ∈ B ∧ C ∈ B ∧ A ⊂ C ∧ ∀ D ∈ B, A ⊂ D → ¬ D ⊂ C

/-- A subcomplex (KP Definition 1.5.1(7)): `B' ⊆ B` containing every facet of `B` that is a
face of one of its members. -/
def IsSubcomplex (B' B : Set (Set X)) : Prop :=
  B' ⊆ B ∧ ∀ A ∈ B', ∀ C ∈ B, C ⊆ A → C ∈ B'

theorem isSubcomplex_refl (B : Set (Set X)) : IsSubcomplex B B :=
  ⟨subset_rfl, fun _ _ _ hC _ => hC⟩

theorem IsSubcomplex.trans {B'' B' B : Set (Set X)} (h₁ : IsSubcomplex B'' B')
    (h₂ : IsSubcomplex B' B) : IsSubcomplex B'' B :=
  ⟨h₁.1.trans h₂.1, fun A hA C hC hCA =>
    h₁.2 A hA C (h₂.2 A (h₁.1 hA) C hC hCA) hCA⟩

/-- A chamber: a maximal facet (KP Definition 1.5.1(9),(10)). -/
def IsChamber (B : Set (Set X)) (C : Set X) : Prop :=
  Maximal (· ∈ B) C

/-- One step `Cᵢ, Cᵢ₊₁` of a gallery (KP Definition 1.5.1(9)): `C` and `D` have a meet `A` in
`B`, the greatest facet of `B` that is a face of both, and `A` has codimension one in `C` and
in `D`. KP writes the meet as `Cᵢ ∩ Cᵢ₊₁ ∈ B`. For subcomplexes of a polysimplicial complex
the two forms agree (`PolysimplicialComplex.isGalleryStep_iff_inter`); the meet form is
invariant under order isomorphisms of `B` (`isGalleryStep_orderIso_iff`). -/
def IsGalleryStep (B : Set (Set X)) (C D : Set X) : Prop :=
  ∃ A, IsGreatest {E | E ∈ B ∧ E ⊆ C ∧ E ⊆ D} A ∧ IsCodimOneFace B A C ∧ IsCodimOneFace B A D

/-- `B`, ordered by inclusion, is a polysimplicial complex (KP Definition 1.5.1(2)) in the sense
of KP Remark 1.5.4: it is order-isomorphic to the set of facets of some polysimplicial complex.
This is how the proof of KP Proposition 1.5.18 gives an ordered set of facets a polysimplicial
structure. -/
def IsPolysimplicial (B : Set (Set X)) : Prop :=
  ∃ (ι : Type u) (_ : Finite ι) (W : ι → Type u) (L : PolysimplicialComplex ι W),
    Nonempty (B ≃o L.facets)

/-- A polysimplicial set of facets is non-empty. -/
theorem IsPolysimplicial.nonempty {B : Set (Set X)} (h : IsPolysimplicial B) : B.Nonempty := by
  obtain ⟨ι, _, W, L, ⟨e⟩⟩ := h
  have x : ∀ i, W i := fun i => Classical.choice (L.factor i).nonempty_vertices
  exact ⟨_, (e.symm ⟨{x}, L.singleton_mem_facets x⟩).2⟩

/-- A chamber complex (KP Definition 1.5.1(9)): a polysimplicial complex (`IsPolysimplicial`)
in which every facet lies in a chamber and any two chambers are joined by a gallery
`C = C₁, …, Cₙ = C'`. -/
def IsChamberComplex (B : Set (Set X)) : Prop :=
  IsPolysimplicial B ∧ (∀ A ∈ B, ∃ C, IsChamber B C ∧ A ⊆ C) ∧
    ∀ C D, IsChamber B C → IsChamber B D → Relation.ReflTransGen (IsGalleryStep B) C D

/-- A facet of codimension one: a codimension-one face of some chamber. -/
def IsCodimOneFacet (B : Set (Set X)) (F : Set X) : Prop :=
  ∃ C, IsChamber B C ∧ IsCodimOneFace B F C

/-- The chambers having `F` as a face. -/
def chambersContaining (B : Set (Set X)) (F : Set X) : Set (Set X) :=
  {C | IsChamber B C ∧ F ⊆ C}

/-- A thick chamber complex (KP Definition 1.5.1(11)): each facet of codimension one is a face
of at least three chambers. -/
def IsThick (B : Set (Set X)) : Prop :=
  IsChamberComplex B ∧ ∀ F, IsCodimOneFacet B F → 3 ≤ (chambersContaining B F).encard

/-- A thin chamber complex (KP Definition 1.5.1(11)): each facet of codimension one is a face
of exactly two chambers. -/
def IsThin (B : Set (Set X)) : Prop :=
  IsChamberComplex B ∧ ∀ F, IsCodimOneFacet B F → (chambersContaining B F).encard = 2

theorem IsChamber.mem {B : Set (Set X)} {C : Set X} (h : IsChamber B C) : C ∈ B :=
  h.1

theorem IsCodimOneFace.ssubset {B : Set (Set X)} {A C : Set X} (h : IsCodimOneFace B A C) :
    A ⊂ C :=
  h.2.2.1

theorem IsChamberComplex.isPolysimplicial {B : Set (Set X)} (h : IsChamberComplex B) :
    IsPolysimplicial B :=
  h.1

theorem IsChamberComplex.nonempty {B : Set (Set X)} (h : IsChamberComplex B) : B.Nonempty :=
  h.1.nonempty

/-- The empty set of facets is not a chamber complex. -/
theorem not_isChamberComplex_empty : ¬ IsChamberComplex (∅ : Set (Set X)) :=
  fun h => Set.not_nonempty_empty h.nonempty

/-- A chamber complex has a chamber. -/
theorem IsChamberComplex.exists_isChamber {B : Set (Set X)} (h : IsChamberComplex B) :
    ∃ C, IsChamber B C :=
  let ⟨A, hA⟩ := h.nonempty
  let ⟨C, hC, _⟩ := h.2.1 A hA
  ⟨C, hC⟩

theorem IsThick.nonempty {B : Set (Set X)} (h : IsThick B) : B.Nonempty :=
  h.1.nonempty

theorem IsThin.nonempty {B : Set (Set X)} (h : IsThin B) : B.Nonempty :=
  h.1.nonempty

theorem IsGalleryStep.mem_left {B : Set (Set X)} {C D : Set X} (h : IsGalleryStep B C D) :
    C ∈ B :=
  let ⟨_, _, h₁, _⟩ := h
  h₁.2.1

theorem IsGalleryStep.mem_right {B : Set (Set X)} {C D : Set X} (h : IsGalleryStep B C D) :
    D ∈ B :=
  let ⟨_, _, _, h₂⟩ := h
  h₂.2.1

theorem IsCodimOneFacet.mem {B : Set (Set X)} {F : Set X} (h : IsCodimOneFacet B F) : F ∈ B :=
  let ⟨_, _, hF⟩ := h
  hF.1

/-! ### Invariance under order isomorphisms

All notions above depend only on `B` as an ordered set: they transfer along an order
isomorphism `B ≃o B'`, as in KP Remark 1.5.4. -/

section OrderIso

variable {Y : Type u} {B : Set (Set X)} {B' : Set (Set Y)}

theorem exists_eq_orderIso (e : B ≃o B') {D : Set Y} (hD : D ∈ B') : ∃ d : B, (e d : Set Y) = D :=
  ⟨e.symm ⟨D, hD⟩, by simp⟩

theorem orderIso_subset_iff (e : B ≃o B') (a b : B) :
    (e a : Set Y) ⊆ e b ↔ (a : Set X) ⊆ b :=
  e.le_iff_le

theorem orderIso_ssubset_iff (e : B ≃o B') (a b : B) :
    (e a : Set Y) ⊂ e b ↔ (a : Set X) ⊂ b :=
  e.lt_iff_lt

theorem isCodimOneFace_orderIso_iff (e : B ≃o B') (a c : B) :
    IsCodimOneFace B' (e a) (e c) ↔ IsCodimOneFace B a c := by
  constructor
  · rintro ⟨-, -, hac, h⟩
    refine ⟨a.2, c.2, (orderIso_ssubset_iff e a c).1 hac, fun D hD had hdc => ?_⟩
    exact h _ (e ⟨D, hD⟩).2 ((orderIso_ssubset_iff e a ⟨D, hD⟩).2 had)
      ((orderIso_ssubset_iff e ⟨D, hD⟩ c).2 hdc)
  · rintro ⟨-, -, hac, h⟩
    refine ⟨(e a).2, (e c).2, (orderIso_ssubset_iff e a c).2 hac, fun D hD had hdc => ?_⟩
    obtain ⟨d, rfl⟩ := exists_eq_orderIso e hD
    exact h d d.2 ((orderIso_ssubset_iff e a d).1 had) ((orderIso_ssubset_iff e d c).1 hdc)

theorem isChamber_orderIso_iff (e : B ≃o B') (c : B) : IsChamber B' (e c) ↔ IsChamber B c := by
  constructor
  · refine fun h => ⟨c.2, fun D hD hcD => ?_⟩
    exact (orderIso_subset_iff e ⟨D, hD⟩ c).1
      (h.2 (e ⟨D, hD⟩).2 ((orderIso_subset_iff e c ⟨D, hD⟩).2 hcD))
  · refine fun h => ⟨(e c).2, fun D hD hcD => ?_⟩
    obtain ⟨d, rfl⟩ := exists_eq_orderIso e hD
    exact (orderIso_subset_iff e d c).2 (h.2 d.2 ((orderIso_subset_iff e c d).1 hcD))

theorem isGalleryStep_orderIso_iff (e : B ≃o B') (c d : B) :
    IsGalleryStep B' (e c) (e d) ↔ IsGalleryStep B c d := by
  constructor
  · rintro ⟨A, ⟨⟨hA, hAc, hAd⟩, hmax⟩, h₁, h₂⟩
    obtain ⟨a, rfl⟩ := exists_eq_orderIso e hA
    refine ⟨a, ⟨⟨a.2, (orderIso_subset_iff e a c).1 hAc, (orderIso_subset_iff e a d).1 hAd⟩,
      fun E hE => ?_⟩, (isCodimOneFace_orderIso_iff e a c).1 h₁,
      (isCodimOneFace_orderIso_iff e a d).1 h₂⟩
    obtain ⟨hE, hEc, hEd⟩ := hE
    exact (orderIso_subset_iff e ⟨E, hE⟩ a).1 (hmax ⟨(e ⟨E, hE⟩).2,
      (orderIso_subset_iff e ⟨E, hE⟩ c).2 hEc, (orderIso_subset_iff e ⟨E, hE⟩ d).2 hEd⟩)
  · rintro ⟨A, ⟨⟨hA, hAc, hAd⟩, hmax⟩, h₁, h₂⟩
    refine ⟨e ⟨A, hA⟩, ⟨⟨(e ⟨A, hA⟩).2, (orderIso_subset_iff e ⟨A, hA⟩ c).2 hAc,
      (orderIso_subset_iff e ⟨A, hA⟩ d).2 hAd⟩, fun E hE => ?_⟩,
      (isCodimOneFace_orderIso_iff e ⟨A, hA⟩ c).2 h₁,
      (isCodimOneFace_orderIso_iff e ⟨A, hA⟩ d).2 h₂⟩
    obtain ⟨hE, hEc, hEd⟩ := hE
    obtain ⟨f, rfl⟩ := exists_eq_orderIso e hE
    exact (orderIso_subset_iff e f ⟨A, hA⟩).2 (hmax ⟨f.2, (orderIso_subset_iff e f c).1 hEc,
      (orderIso_subset_iff e f d).1 hEd⟩)

theorem isCodimOneFacet_orderIso_iff (e : B ≃o B') (f : B) :
    IsCodimOneFacet B' (e f) ↔ IsCodimOneFacet B f := by
  constructor
  · rintro ⟨C, hC, hfC⟩
    obtain ⟨c, rfl⟩ := exists_eq_orderIso e hC.mem
    exact ⟨c, (isChamber_orderIso_iff e c).1 hC, (isCodimOneFace_orderIso_iff e f c).1 hfC⟩
  · rintro ⟨C, hC, hfC⟩
    exact ⟨e ⟨C, hC.mem⟩, (isChamber_orderIso_iff e _).2 hC,
      (isCodimOneFace_orderIso_iff e f ⟨C, hC.mem⟩).2 hfC⟩

/-- An order isomorphism `e : B ≃o B'` matches the chambers of `B` through a facet `f` with
the chambers of `B'` through `e f`. -/
def chambersContainingOrderIsoEquiv (e : B ≃o B') (f : B) :
    chambersContaining B f ≃ chambersContaining B' (e f) where
  toFun C := ⟨e ⟨C, C.2.1.mem⟩, (isChamber_orderIso_iff e _).2 C.2.1,
    (orderIso_subset_iff e f ⟨C, C.2.1.mem⟩).2 C.2.2⟩
  invFun C := ⟨e.symm ⟨C, C.2.1.mem⟩,
    (isChamber_orderIso_iff e _).1 (by simpa using C.2.1),
    (orderIso_subset_iff e f _).1 (by simpa using C.2.2)⟩
  left_inv C := Subtype.ext (by simp)
  right_inv C := Subtype.ext (by simp)

theorem encard_chambersContaining_orderIso (e : B ≃o B') (f : B) :
    (chambersContaining B' (e f)).encard = (chambersContaining B f).encard :=
  (Set.encard_congr (chambersContainingOrderIsoEquiv e f)).symm

theorem IsPolysimplicial.of_orderIso (e : B ≃o B') (h : IsPolysimplicial B) :
    IsPolysimplicial B' :=
  let ⟨ι, hι, W, L, ⟨f⟩⟩ := h
  ⟨ι, hι, W, L, ⟨e.symm.trans f⟩⟩

theorem IsChamberComplex.of_orderIso (e : B ≃o B') (h : IsChamberComplex B) :
    IsChamberComplex B' := by
  classical
  refine ⟨h.1.of_orderIso e, fun A hA => ?_, fun C D hC hD => ?_⟩
  · obtain ⟨a, rfl⟩ := exists_eq_orderIso e hA
    obtain ⟨C, hC, haC⟩ := h.2.1 a a.2
    exact ⟨e ⟨C, hC.mem⟩, (isChamber_orderIso_iff e _).2 hC,
      (orderIso_subset_iff e a ⟨C, hC.mem⟩).2 haC⟩
  · obtain ⟨c, rfl⟩ := exists_eq_orderIso e hC.mem
    obtain ⟨d, rfl⟩ := exists_eq_orderIso e hD.mem
    -- Extend `e` to all subsets of `X` to transport the intermediate chambers of a gallery.
    let g : Set X → Set Y := fun S => if hS : S ∈ B then e ⟨S, hS⟩ else ∅
    have hg : ∀ s : B, g s = e s := fun s => dite_eq_left s.2
    have key : Relation.ReflTransGen (IsGalleryStep B') (g c) (g d) :=
      Relation.ReflTransGen.lift g (p := IsGalleryStep B') (fun S T hST => by
          change IsGalleryStep B' (g S) (g T)
          rw [show g S = e ⟨S, hST.mem_left⟩ from dite_eq_left hST.mem_left,
            show g T = e ⟨T, hST.mem_right⟩ from dite_eq_left hST.mem_right]
          exact (isGalleryStep_orderIso_iff e _ _).2 hST) _ _
        (h.2.2 c d ((isChamber_orderIso_iff e c).1 hC) ((isChamber_orderIso_iff e d).1 hD))
    rwa [hg c, hg d] at key

theorem IsThick.of_orderIso (e : B ≃o B') (h : IsThick B) : IsThick B' := by
  refine ⟨h.1.of_orderIso e, fun F hF => ?_⟩
  obtain ⟨f, rfl⟩ := exists_eq_orderIso e hF.mem
  rw [encard_chambersContaining_orderIso]
  exact h.2 f ((isCodimOneFacet_orderIso_iff e f).1 hF)

theorem IsThin.of_orderIso (e : B ≃o B') (h : IsThin B) : IsThin B' := by
  refine ⟨h.1.of_orderIso e, fun F hF => ?_⟩
  obtain ⟨f, rfl⟩ := exists_eq_orderIso e hF.mem
  rw [encard_chambersContaining_orderIso]
  exact h.2 f ((isCodimOneFacet_orderIso_iff e f).1 hF)

theorem isChamberComplex_orderIso_iff (e : B ≃o B') :
    IsChamberComplex B' ↔ IsChamberComplex B :=
  ⟨fun h => h.of_orderIso e.symm, fun h => h.of_orderIso e⟩

theorem isThick_orderIso_iff (e : B ≃o B') : IsThick B' ↔ IsThick B :=
  ⟨fun h => h.of_orderIso e.symm, fun h => h.of_orderIso e⟩

theorem isThin_orderIso_iff (e : B ≃o B') : IsThin B' ↔ IsThin B :=
  ⟨fun h => h.of_orderIso e.symm, fun h => h.of_orderIso e⟩

end OrderIso

end ChamberComplex

namespace PolysimplicialComplex

variable {ι : Type v} [Finite ι] {V : ι → Type u}

/-- The facets of a polysimplicial complex form a polysimplicial complex in the sense of
`IsPolysimplicial`. The witness is `K` itself, with index and vertex types lifted to the universe
of `∀ i, V i`. -/
theorem isPolysimplicial_facets (K : PolysimplicialComplex ι V) : IsPolysimplicial K.facets := by
  let L : PolysimplicialComplex (ULift.{u} ι) (fun j => ULift.{v} (V j.down)) :=
    ⟨fun j => (K.factor j.down).congr Equiv.ulift.symm⟩
  let e : (∀ i, (K.factor i).faces) ≃o ∀ j, (L.factor j).faces :=
    { toFun := fun s j => (K.factor j.down).congrFacesOrderIso Equiv.ulift.symm (s j.down)
      invFun := fun t i => ((K.factor i).congrFacesOrderIso Equiv.ulift.symm).symm (t ⟨i⟩)
      left_inv := fun s => funext fun i => OrderIso.symm_apply_apply _ _
      right_inv := fun t => funext fun j => OrderIso.apply_symm_apply _ _
      map_rel_iff' := ⟨fun h i => ((K.factor i).congrFacesOrderIso Equiv.ulift.symm).le_iff_le.1
          (h ⟨i⟩),
        fun h j => ((K.factor j.down).congrFacesOrderIso Equiv.ulift.symm).le_iff_le.2
          (h j.down)⟩ }
  exact ⟨ULift.{u} ι, inferInstance, _, L, ⟨(K.facetsOrderIso.trans e).trans L.facetsOrderIso.symm⟩⟩

/-- For a subcomplex `B` of a polysimplicial complex `K`, a gallery step is KP's literal
condition (Definition 1.5.1(9)): `C ∩ D ∈ B`, of codimension one in `C` and in `D`. This applies
to `B = K.facets` (`isSubcomplex_refl`) and to the apartments of a building. -/
theorem isGalleryStep_iff_inter (K : PolysimplicialComplex ι V) {B : Set (Set (∀ i, V i))}
    (hB : IsSubcomplex B K.facets) {C D : Set (∀ i, V i)} :
    IsGalleryStep B C D ↔
      C ∩ D ∈ B ∧ IsCodimOneFace B (C ∩ D) C ∧ IsCodimOneFace B (C ∩ D) D := by
  constructor
  · rintro ⟨A, ⟨⟨hA, hAC, hAD⟩, hmax⟩, h₁, h₂⟩
    have hCD : C ∩ D ∈ B := hB.2 C h₁.2.1 _
      (inter_mem_facets (hB.1 h₁.2.1) (hB.1 h₂.2.1)
        ((nonempty_of_mem_facets (hB.1 hA)).mono (Set.subset_inter hAC hAD)))
      Set.inter_subset_left
    have hA' : A = C ∩ D := (Set.subset_inter hAC hAD).antisymm
      (hmax ⟨hCD, Set.inter_subset_left, Set.inter_subset_right⟩)
    subst hA'
    exact ⟨hCD, h₁, h₂⟩
  · rintro ⟨hCD, h₁, h₂⟩
    exact ⟨C ∩ D, ⟨⟨hCD, Set.inter_subset_left, Set.inter_subset_right⟩,
      fun E hE => Set.subset_inter hE.2.1 hE.2.2⟩, h₁, h₂⟩

end PolysimplicialComplex

/-! ### Isomorphisms -/

/-- An isomorphism of simplicial complexes (KP Definition 1.5.1(12)): a bijection of vertices
mapping simplices to simplices, whose inverse also maps simplices to simplices. -/
structure SimplicialIso {V₁ : Type u} {V₂ : Type w} (K₁ : SimplicialComplex V₁)
    (K₂ : SimplicialComplex V₂) where
  toEquiv : V₁ ≃ V₂
  image_mem : ∀ s ∈ K₁.faces, toEquiv '' s ∈ K₂.faces
  preimage_mem : ∀ s ∈ K₂.faces, toEquiv ⁻¹' s ∈ K₁.faces

/-- An isomorphism of polysimplicial complexes (KP Definition 1.5.1(13)): a bijection `σ` of
the index sets and isomorphisms `Bᵢ → B'_{σ(i)}`. -/
structure PolysimplicialIso {ι : Type v} [Finite ι] {V : ι → Type u} {ι' : Type v} [Finite ι']
    {V' : ι' → Type w} (K : PolysimplicialComplex ι V) (K' : PolysimplicialComplex ι' V') where
  perm : ι ≃ ι'
  factorIso : ∀ i, SimplicialIso (K.factor i) (K'.factor (perm i))

namespace PolysimplicialIso

variable {ι : Type v} [Finite ι] {V : ι → Type u} {ι' : Type v} [Finite ι'] {V' : ι' → Type w}
  {K : PolysimplicialComplex ι V} {K' : PolysimplicialComplex ι' V'}

/-- The induced bijection `V₁ × ⋯ × Vₙ → V'₁ × ⋯ × V'ₙ` of vertex sets. -/
def vertexEquiv (φ : PolysimplicialIso K K') : (∀ i, V i) ≃ (∀ j, V' j) :=
  Equiv.piCongr φ.perm fun i => (φ.factorIso i).toEquiv

theorem vertexEquiv_apply_apply (φ : PolysimplicialIso K K') (x : ∀ i, V i) (i : ι) :
    φ.vertexEquiv x (φ.perm i) = (φ.factorIso i).toEquiv (x i) :=
  Equiv.piCongr_apply_apply _ _ x i

/-- The preimage of a facet under the vertex bijection of an isomorphism is a facet. -/
theorem preimage_mem_facets (φ : PolysimplicialIso K K') {F : Set (∀ j, V' j)}
    (hF : F ∈ K'.facets) : φ.vertexEquiv ⁻¹' F ∈ K.facets := by
  obtain ⟨t, ht, rfl⟩ := hF
  refine ⟨fun i => (φ.factorIso i).toEquiv ⁻¹' t (φ.perm i),
    fun i => (φ.factorIso i).preimage_mem _ (ht _), ?_⟩
  ext x
  simp only [Set.mem_preimage, Set.mem_univ_pi]
  constructor
  · intro h i
    have := h (φ.perm i)
    rwa [vertexEquiv_apply_apply] at this
  · intro h j
    obtain ⟨i, rfl⟩ := φ.perm.surjective j
    rw [vertexEquiv_apply_apply]
    exact h i

end PolysimplicialIso

/-- A permutation of the vertex set is a polysimplicial automorphism if it is the vertex
bijection of an isomorphism `K → K` (KP Definition 1.5.1(13)). -/
def IsPolysimplicialAutomorphism {ι : Type v} [Finite ι] {V : ι → Type u}
    (K : PolysimplicialComplex ι V) (e : (∀ i, V i) ≃ (∀ i, V i)) : Prop :=
  ∃ φ : PolysimplicialIso K K, φ.vertexEquiv = e

/-! ### Buildings -/

/-- A building (KP Definition 1.5.5): a polysimplicial complex `K` with a collection of
subcomplexes, the apartments (each given by its set of facets), such that

* BL 1: `K` is a thick chamber complex;
* BL 2: each apartment is a thin chamber complex;
* BL 3: any two chambers belong to an apartment;
* BL 4: for apartments `𝒜₁, 𝒜₂` and facets `F₁, F₂ ∈ 𝒜₁ ∩ 𝒜₂` there is an isomorphism
  `𝒜₁ → 𝒜₂` fixing `F₁`, `F₂` and all their faces; an isomorphism of apartments is an
  isomorphism of their ordered sets of facets (KP Remark 1.5.4). -/
structure IsBuilding {ι : Type v} [Finite ι] {V : ι → Type u} (K : PolysimplicialComplex ι V)
    (apartments : Set (Set (Set (∀ i, V i)))) : Prop where
  thick : IsThick K.facets
  isSubcomplex : ∀ 𝒜 ∈ apartments, IsSubcomplex 𝒜 K.facets
  thin : ∀ 𝒜 ∈ apartments, IsThin 𝒜
  exists_apartment : ∀ C D, IsChamber K.facets C → IsChamber K.facets D →
    ∃ 𝒜 ∈ apartments, C ∈ 𝒜 ∧ D ∈ 𝒜
  exists_orderIso : ∀ 𝒜₁ ∈ apartments, ∀ 𝒜₂ ∈ apartments, ∀ F₁ ∈ 𝒜₁ ∩ 𝒜₂, ∀ F₂ ∈ 𝒜₁ ∩ 𝒜₂,
    ∃ φ : 𝒜₁ ≃o 𝒜₂, ∀ (F : Set (∀ i, V i)) (hF : F ∈ 𝒜₁), (F ⊆ F₁ ∨ F ⊆ F₂) →
      ((φ ⟨F, hF⟩ : 𝒜₂) : Set (∀ i, V i)) = F

theorem IsBuilding.isChamberComplex {ι : Type v} [Finite ι] {V : ι → Type u}
    {K : PolysimplicialComplex ι V} {apartments : Set (Set (Set (∀ i, V i)))}
    (h : IsBuilding K apartments) : IsChamberComplex K.facets :=
  h.thick.1

/-- Every apartment of a building has a facet; in particular `∅` is not an apartment. -/
theorem IsBuilding.nonempty_of_mem {ι : Type v} [Finite ι] {V : ι → Type u}
    {K : PolysimplicialComplex ι V} {apartments : Set (Set (Set (∀ i, V i)))}
    (h : IsBuilding K apartments) {𝒜 : Set (Set (∀ i, V i))} (h𝒜 : 𝒜 ∈ apartments) :
    𝒜.Nonempty :=
  (h.thin 𝒜 h𝒜).nonempty

theorem IsBuilding.empty_not_mem {ι : Type v} [Finite ι] {V : ι → Type u}
    {K : PolysimplicialComplex ι V} {apartments : Set (Set (Set (∀ i, V i)))}
    (h : IsBuilding K apartments) : ∅ ∉ apartments :=
  fun h0 => Set.not_nonempty_empty (h.nonempty_of_mem h0)

end Langlands.Geometry.Building.AbstractBuilding
