# Kaletha–Prasad abstract buildings: polysimplicial complexes, chamber complexes, buildings

Module `Langlands.Geometry.Building.AbstractBuilding`, namespace
`Langlands.Geometry.Building.AbstractBuilding`.

This module formalizes the combinatorial definitions at the start of Kaletha–Prasad,
*Bruhat–Tits Theory: A New Approach* (2023), §1.5 "Abstract Buildings" (book PDF
pp. 85–86, printed pp. 54–55). These are Definition 1.5.1 (simplicial and polysimplicial
complexes, facets, faces, codimension, subcomplexes, chamber complexes, galleries, thick
and thin complexes, isomorphisms) and Definition 1.5.5 (buildings, axioms BL 1–BL 4).
The *Corrections and additions* of 1 November 2024 change neither definition. Their
§1.5 items concern Propositions 1.5.6, 1.5.18 and 1.5.28 and Definitions 1.5.17 and 1.5.20,
none of which is formalized here. Remark 1.5.4 and the proof of Proposition 1.5.18 are used
to read "is a polysimplicial complex" for a set of facets (see `IsPolysimplicial`).

KP Axiom 4.1.1 asks for "a building `B = B(G)` in the sense of Definition 1.5.5, equipped
with an action of `G(k)` by polysimplicial automorphisms". This module supplies that
vocabulary. No group, field, Tits system, reductive group, apartment of a reductive group or
geometric realization is involved.

## Simplicial and polysimplicial complexes

- `SimplicialComplex V` is KP Definition 1.5.1(1). Its fields are:
  - `faces : Set (Set V)`, the simplices;
  - `nonempty_vertices : Nonempty V`;
  - `finite_of_mem` and `nonempty_of_mem`: every simplex is a finite non-empty subset;
  - `singleton_mem`: `{x}` is a simplex for every vertex `x`;
  - `mem_of_subset`: every non-empty subset of a simplex is a simplex.

  KP's "non-empty set `B` of non-empty finite subsets" is the field list above, and
  `SimplicialComplex.faces_nonempty` proves that `B` is non-empty. Simplices are `Set V` with
  an explicit finiteness field, rather than `Finset V`, so no decidable equality on vertices
  is needed. The empty set is excluded, as KP Remark 1.5.3 requires.
- `PolysimplicialComplex ι V` is KP Definition 1.5.1(2): a family `factor i` of simplicial
  complexes on vertex types `V i`, indexed by a finite type `ι` (`[Finite ι]`). KP writes the
  family as a tuple `(B₁, …, Bₙ)`. Indexing by an arbitrary finite type is equivalent, by
  enumerating `ι`, and lets the factors be indexed by, for example, irreducible components.
- `PolysimplicialComplex.facets K : Set (Set (∀ i, V i))` is the set of facets
  `A₁ × ⋯ × Aₙ = Set.univ.pi s` with `s i ∈ (K.factor i).faces`. This is KP's
  `B = B₁ × ⋯ × Bₙ` as a set of subsets of `V = V₁ × ⋯ × Vₙ` (Definition 1.5.1(2),(3)).
  So facets are literally subsets of the product vertex set. "Face" (Definition 1.5.1(4))
  is inclusion `⊆`, and for subcomplexes of `K` the intersection in Definition 1.5.1(9) is
  `∩` (`isGalleryStep_iff_inter` below). A simplicial complex is the one-factor case.
- Laws:
  - `mem_facets` and `pi_mem_facets`.
  - `singleton_mem_facets`: every vertex `{x}` is a facet.
  - `nonempty_of_mem_facets` and `finite_of_mem_facets`.
  - `inter_mem_facets`: if two facets meet, their intersection is a facet, since
    `∏ᵢ sᵢ ∩ ∏ᵢ tᵢ = ∏ᵢ (sᵢ ∩ tᵢ)` and a non-empty subset of a simplex is a simplex.
  - `PolysimplicialComplex.pi_subset_pi_iff`: if `Set.univ.pi s` is a facet, then
    `Set.univ.pi s ⊆ Set.univ.pi t ↔ ∀ i, s i ⊆ t i`. So the face relation on products is
    componentwise.
  - `PolysimplicialComplex.facetsOrderIso K : K.facets ≃o ∀ i, (K.factor i).faces`: the
    facets ordered by inclusion are the tuples of simplices with the product order. It sends
    a facet `F` to its coordinate projections `(fun x => x i) '' F` and has inverse
    `s ↦ Set.univ.pi s`. This is KP's `B = B₁ × ⋯ × Bₙ` read literally as a product of sets.
- Auxiliary transport: `SimplicialComplex.congr K f` is the simplicial complex on `W`
  obtained from `K` on `V` along a bijection `f : V ≃ W` (simplices: the sets whose
  preimage is a simplex). `SimplicialComplex.congrFacesOrderIso K f` is the induced order
  isomorphism of simplex sets, `s ↦ f '' s`. These are used only to change universes in
  `isPolysimplicial_facets`.

## Faces, subcomplexes and chamber complexes

These notions are defined for an arbitrary set `B : Set (Set X)` of facets, ordered by
inclusion. KP applies them both to the whole complex and to subcomplexes such as apartments
(BL 2). For a polysimplicial complex `K` one takes `B = K.facets`.

- `IsCodimOneFace B A C` means `codim(A, C) = 1` (KP Definition 1.5.1(5)): `A` and `C` are
  in `B`, `A ⊊ C`, and no `D ∈ B` satisfies `A ⊊ D ⊊ C`. KP defines `codim(A, C)` as the
  largest `n` with a chain `A = A₀ ⊊ A₁ ⊊ ⋯ ⊊ Aₙ = C` in `B`, so `codim(A, C) = 1` is exactly
  this condition. General codimension and dimension (Definition 1.5.1(5),(6)) and the
  open star (Definition 1.5.1(8)) are not defined.
- `IsSubcomplex B' B` is KP Definition 1.5.1(7): `B' ⊆ B`, and a facet of `B` contained in a
  member of `B'` belongs to `B'`. `isSubcomplex_refl` and `IsSubcomplex.trans` are proved.
- `IsChamber B C` says `C` is a maximal element of `B` (Mathlib's `Maximal (· ∈ B) C`), as
  in KP Definition 1.5.1(10).
- `IsGalleryStep B C D` is one step `Cᵢ, Cᵢ₊₁` of a gallery (KP Definition 1.5.1(9)). KP
  asks that `Cᵢ ∩ Cᵢ₊₁ ∈ B` have codimension one in `Cᵢ` and in `Cᵢ₊₁`. The definition uses
  the meet of `C` and `D` in the ordered set `B` instead: there is an `A` that is the greatest
  element (`IsGreatest`) of `{E ∈ B | E ⊆ C ∧ E ⊆ D}`, with `codim(A, C) = codim(A, D) = 1`.
  This is a derived formulation, and it agrees with KP's wherever KP uses galleries:
  - `PolysimplicialComplex.isGalleryStep_iff_inter K hB`: if `B` is a subcomplex of
    `K.facets`, then `IsGalleryStep B C D` holds exactly when `C ∩ D ∈ B` and
    `codim(C ∩ D, C) = codim(C ∩ D, D) = 1`. This covers `B = K.facets` itself
    (`isSubcomplex_refl`) and the apartments of a building. The proof: the meet `A` is a
    non-empty common face of the facets `C` and `D` of `K`. So `C ∩ D` is a facet of `K`
    (`inter_mem_facets`), and it lies in `B` because `B` is a subcomplex and `C ∩ D ⊆ C`.
    Hence `C ∩ D` is the greatest common face, `A = C ∩ D`.
  - Unlike the literal intersection, the meet depends only on `B` as an ordered set
    (`isGalleryStep_orderIso_iff`). This matters because `IsPolysimplicial` below only
    provides an order isomorphism to the facets of a polysimplicial complex. For example,
    `B = {{a}, {b}, {c}, {a, b, d}, {b, c, d}}` is order-isomorphic to the facets of the path
    `a – b – c`. Its two chambers meet in `{b}` in `B`, but `{a, b, d} ∩ {b, c, d} = {b, d}` is
    not in `B`. With the literal intersection, `B` would be polysimplicial with no gallery
    between its chambers, while the path has one. With the meet there is a one-step gallery
    through `{b}`.
- `IsPolysimplicial B` says that `B`, ordered by inclusion, is a polysimplicial complex:
  there are a finite type `ι`, vertex types `W i` and `L : PolysimplicialComplex ι W` with an
  order isomorphism `B ≃o L.facets`. This reads KP's "is a polysimplicial complex" for a set of
  facets, as needed in Definition 1.5.1(9) for apartments (BL 2). Two places in KP fix this
  reading:
  - Remark 1.5.4 presents a (poly)simplicial complex as an ordered set: the vertices are
    recovered as the minimal elements.
  - The proof of Proposition 1.5.18 (book PDF p. 93, printed p. 62) gives the set `B′` of
    admissible facets of a simplicial building "the structure of a polysimplicial complex"
    by an order-preserving bijection `B′ → ∏ Bᵢ`.

  A literal reading is impossible for an apartment `𝒜 ⊆ K.facets`. Being of the form
  `B₁ × ⋯ × Bₙ` over the same vertex set `V₁ × ⋯ × Vₙ` would, by the singleton axiom of
  Definition 1.5.1(1), force every vertex of `K` into `𝒜`.

  The index and vertex types are taken in the universe of the ambient type `X`. This loses
  nothing: the vertices of `L` correspond to the minimal elements of `B`, which are subsets
  of `X`, so each `W i` is no larger than `Set X`. This remark is not formalized.
  - `IsPolysimplicial.nonempty`: a polysimplicial `B` is non-empty, since `L` has a vertex.
  - `PolysimplicialComplex.isPolysimplicial_facets K`: `K.facets` is polysimplicial. The
    witness is `K` itself with `ι` and the `V i` lifted by `ULift` to the universe of
    `∀ i, V i`. The order isomorphism is `facetsOrderIso K`, then `congrFacesOrderIso` in each
    factor, then the inverse of `facetsOrderIso` for the lifted complex.
- `IsChamberComplex B` is KP Definition 1.5.1(9). It has three clauses:
  - `IsPolysimplicial B`: in KP a chamber complex is a polysimplicial complex. In
    particular `B` is non-empty; without this clause the empty set would satisfy the other
    two vacuously.
  - Every facet lies in a chamber.
  - Any two chambers `C, C'` are joined by a sequence `C = C₁, …, Cₙ = C'` of gallery
    steps, stated as `Relation.ReflTransGen (IsGalleryStep B) C C'`. As in KP, the
    intermediate `Cᵢ` are required to be facets of `B`, which the gallery-step condition
    forces, but not to be maximal.

  For `B = K.facets` the first clause always holds (`isPolysimplicial_facets`). For an
  apartment it excludes sets of facets with no product structure. For example, the boundary
  of a cube inside a product of three 1-simplices is a non-empty, gallery-connected
  subcomplex in which every edge lies in exactly two squares. It is not polysimplicial: at a
  vertex, any two of the three edge directions span a square, so they would lie in three
  different factors. Then the product of the three edges would be a facet with eight
  vertices, which the cube boundary lacks. This example is explained here, not formalized.
- `IsCodimOneFacet B F` says `F` is a codimension-one face of some chamber. KP's
  "facet of codimension 1" in Definition 1.5.1(11) is read this way. This is a derived
  formulation: the module does not prove that all chambers of a chamber complex have the
  same dimension, which would make the reading independent of the chamber.
- `chambersContaining B F` is the set of chambers having `F` as a face.
- `IsThick B` is KP Definition 1.5.1(11): a chamber complex in which each facet of
  codimension one is a face of at least three chambers (`3 ≤ encard`). `IsThin B` is the
  same with exactly two chambers (`encard = 2`). `Set.encard` counts in `ℕ∞`, so an
  infinite set of chambers counts as at least three. Both include `IsChamberComplex B`, so
  both require `B` to be polysimplicial and hence non-empty.
- Laws:
  - `IsChamber.mem` and `IsCodimOneFace.ssubset` (the strict inclusion).
  - `IsChamberComplex.isPolysimplicial`.
  - `IsChamberComplex.nonempty`, `IsThick.nonempty` and `IsThin.nonempty`.
  - `not_isChamberComplex_empty`: the empty set of facets is not a chamber complex.
  - `IsChamberComplex.exists_isChamber`: a chamber complex has a chamber.
  - `IsGalleryStep.mem_left`, `IsGalleryStep.mem_right` and `IsCodimOneFacet.mem`: the
    facets involved belong to `B`.

## Invariance under order isomorphisms

All the notions above depend only on `B` as an ordered set, as KP Remark 1.5.4 presents
complexes. For `B : Set (Set X)`, `B' : Set (Set Y)` with `X` and `Y` in the same universe,
and an order isomorphism `e : B ≃o B'`:

- `exists_eq_orderIso`, `orderIso_subset_iff` and `orderIso_ssubset_iff`: every member of `B'`
  is some `e d`, and `e` preserves and reflects `⊆` and `⊂`.
- `isCodimOneFace_orderIso_iff`, `isChamber_orderIso_iff`, `isGalleryStep_orderIso_iff` and
  `isCodimOneFacet_orderIso_iff`: each notion holds for the images under `e` in `B'` exactly
  when it holds in `B`.
- `chambersContainingOrderIsoEquiv e f` is the bijection `C ↦ e C` from the chambers of `B`
  through `f` to the chambers of `B'` through `e f`. `encard_chambersContaining_orderIso` says
  the two counts agree.
- `IsPolysimplicial.of_orderIso`, `IsChamberComplex.of_orderIso`, `IsThick.of_orderIso` and
  `IsThin.of_orderIso` transfer the predicates from `B` to `B'`. For galleries, `e` is
  extended to all subsets of `X` and each gallery step is mapped by
  `isGalleryStep_orderIso_iff`. The equivalences `isChamberComplex_orderIso_iff`,
  `isThick_orderIso_iff` and `isThin_orderIso_iff` follow.

In particular, if `B ≃o L.facets` exhibits `B` as polysimplicial, then `B` is a (thin, thick)
chamber complex exactly when `L.facets` is.

## Isomorphisms and automorphisms

- `SimplicialIso K₁ K₂` is KP Definition 1.5.1(12): a bijection `toEquiv : V₁ ≃ V₂` such
  that `toEquiv '' s` is a simplex for every simplex `s` of `K₁` (`image_mem`), and
  `toEquiv ⁻¹' s` is a simplex for every simplex `s` of `K₂` (`preimage_mem`).
- `PolysimplicialIso K K'` is KP Definition 1.5.1(13): a bijection `perm : ι ≃ ι'` of index
  sets and isomorphisms `factorIso i : SimplicialIso (K.factor i) (K'.factor (perm i))`.
- `PolysimplicialIso.vertexEquiv φ : (∀ i, V i) ≃ (∀ j, V' j)` is the induced bijection of
  product vertex sets, Mathlib's `Equiv.piCongr`. `vertexEquiv_apply_apply` is its
  defining formula `(φ.vertexEquiv x) (perm i) = factorIso i (x i)`.
- `PolysimplicialIso.preimage_mem_facets`: the preimage of a facet of `K'` under
  `vertexEquiv` is a facet of `K`.
- `IsPolysimplicialAutomorphism K e` says the permutation `e` of the vertex set
  `∀ i, V i` is `vertexEquiv φ` for some `φ : PolysimplicialIso K K`. KP's "action of `G(k)`
  by polysimplicial automorphisms" (Axiom 4.1.1) is then an action whose every element
  satisfies this predicate. KP Definition 1.5.1(14), isomorphisms of chamber complexes,
  is not defined separately.

## Buildings

`IsBuilding K apartments` is KP Definition 1.5.5. It is a `Prop`-valued structure for a
polysimplicial complex `K` and a set `apartments`, each apartment given by its set of
facets. Its fields are:

- `thick`: BL 1, `K.facets` is a thick chamber complex.
- `isSubcomplex`: apartments are subcomplexes of `K`. Definition 1.5.5 calls them
  subcomplexes.
- `thin`: BL 2, each apartment is a thin chamber complex. In particular every apartment
  is polysimplicial in the sense of `IsPolysimplicial` and has a facet, so `∅` is not an
  apartment. Since apartments are subcomplexes, their gallery steps are KP's literal ones
  (`isGalleryStep_iff_inter`).
- `exists_apartment`: BL 3, any two chambers of `K` belong to a common apartment.
- `exists_orderIso`: BL 4. For apartments `𝒜₁, 𝒜₂` and facets `F₁, F₂ ∈ 𝒜₁ ∩ 𝒜₂`, there
  is an isomorphism `φ : 𝒜₁ ≃o 𝒜₂` that fixes every facet `F` of `𝒜₁` with `F ⊆ F₁` or
  `F ⊆ F₂`, including `F₁` and `F₂`. This fixes `F₁`, `F₂` and all their faces, as BL 4
  asks.

  Derived point: an apartment is a subcomplex given only as a set of facets. Its
  polysimplicial structure exists only up to an order isomorphism (`IsPolysimplicial`), as
  in the proof of KP Proposition 1.5.18. So "isomorphism `A₁ → A₂`" is formalized as an
  isomorphism of the ordered sets of facets, following KP Remark 1.5.4. Two facts, not
  formalized here, relate this to Definition 1.5.1(13):
  - An isomorphism `(σ, fᵢ)` of polysimplicial complexes induces a bijection of vertex sets
    that maps facets onto facets (compare `PolysimplicialIso.preimage_mem_facets`), and hence
    an order isomorphism of facet sets.
  - Conversely, an order isomorphism `φ : A₁ ≃o A₂` is an isomorphism of polysimplicial
    complexes once `A₁` carries the structure transported from `A₂` along `φ`.

  So the order-isomorphism form is the reading that does not depend on a chosen structure.
  KP notes after BL 4 that the isomorphism need not extend to `B`, and the formalization
  asks for no extension.

Laws:

- `IsBuilding.isChamberComplex` extracts the chamber-complex property of `K`.
- `IsBuilding.nonempty_of_mem`: every apartment is non-empty.
- `IsBuilding.empty_not_mem`: `∅` is not an apartment.

## Scope and provenance

- Source: Kaletha–Prasad (2023), registered as
  `kaletha-prasad-2023-bruhat-tits-new-approach`, SHA256
  `05ad9a284a2577b34d1a270228b74dfb28f520561ae7772d8f38dddb78938732`. The items used are
  Definition 1.5.1 and Remarks 1.5.3–1.5.4 (book PDF pp. 85–86) and Definition 1.5.5
  (book PDF pp. 86–87). The proof of Proposition 1.5.18 (book PDF p. 93) is cited for the
  reading of `IsPolysimplicial`. The corrections
  (`kaletha-prasad-2024-corrections`, SHA256
  `23293f51e58d5ceecb91f834743f68058b98431797d2531142415d013fdf61ed`, §1.5 items on
  PDF pp. 20–21) do not touch these definitions. Their change to the proof of
  Proposition 1.5.18 (PDF p. 21: `P_{Sᵢᶜ}` becomes `G_{Sᵢᶜ}`) does not affect the
  order-bijection step cited here.
- Derived formulations, explained above:
  - simplices as finite `Set`s;
  - a finite index type instead of `{1, …, n}`;
  - codimension one as "no facet strictly between";
  - gallery steps through the meet of two facets in `B`, which is their intersection on
    subcomplexes of a polysimplicial complex (`isGalleryStep_iff_inter`);
  - "facet of codimension one" as a codimension-one face of some chamber;
  - `encard` counts;
  - chamber-complex notions for arbitrary facet sets;
  - "is a polysimplicial complex" for a set of facets as order-isomorphic to the facets of a
    polysimplicial complex, with index and vertex types in the universe of the ambient
    type (Remark 1.5.4 and the proof of Proposition 1.5.18);
  - BL 4 isomorphisms as order isomorphisms of facet sets (Remark 1.5.4);
  - polysimplicial automorphisms as vertex permutations induced by self-isomorphisms.
- Not formalized:
  - general codimension and dimension, open stars, and isomorphisms of chamber complexes;
  - the building of a Tits system (Proposition 1.5.6) and the restricted building
    (Proposition 1.5.18);
  - geometric realizations, metrics, and any statement that a building exists for a
    reductive group (KP Axiom 4.1.1 is an axiom, verified in Chapters 7–9).
