# Renard A.VI.2: sums of indexed families of subobjects

This unit constructs the sum of an arbitrary indexed family of subobjects as the image of the coproduct map, and proves that it is the least upper bound of the family in Mathlib's existing order on subobjects. It realizes the source remark after AB5 in Renard's Appendix A.VI.2, printed page 263 / PDF269: the sums in AB5 exist because of AB4\*. Module: `Langlands.CategoryTheory.Renard.IndexedSubobjectSums`, namespace `Langlands.Renard`. It imports `Langlands.CategoryTheory.RenardGrothendieckAxioms` unchanged.

The unit proves existence of sums and the intrinsic laws of the construction. It does not prove the AB5 distributivity law `N ∩ (∑ᵢ Mᵢ) = ∑ᵢ (N ∩ Mᵢ)`, which is an axiom in the source.

## Source and reading record

The governing original is David Renard, *Représentations des groupes réductifs p-adiques*, French edition dated 9 July 2026, registered source `renard-2026-representations-groupes-reductifs-padiques`, SHA256 `7b539996793b7c3620e72e1e389588eb42d1a8e91d6f68b2eead5c2e2ffc182c`, file `/home/taskhub/central-library/Renard--Representations des groupes reductifs p-adiques (2026 version)--2026.pdf`. The hash was recomputed at authoring. PDF268–270 (printed pages 262–264) were read in full.

In translation, the relevant statements are:

- PDF268, A.VI.2(3): two subobjects of an object have an intersection and a union. In abelian categories the source calls unions *sums*, written `+` or `∑`.
- PDF268, before A.VI.2(4): the *image* of a morphism `f : A → B` is the smallest subobject `C → B` of `B` through which `f` factors.
- PDF269: AB4\* says that every family of objects has a direct sum. AB5 says that the category is cocomplete and that `N ∩ (∑ᵢ Mᵢ) = ∑ᵢ (N ∩ Mᵢ)` for every filtered increasing system `Mᵢ` of subobjects of `M` and every subobject `N`. The source then remarks: "Remarquons que les sommes existent grâce à AB4\*" ("note that the sums exist thanks to AB4\*").
- PDF270 (A.VI.3, after AB6) uses such sums for arbitrary families: the union of a chain of proper subobjects in the Zorn argument of the Proposition, and `JH(∑_{i∈I} Mᵢ) = ⋃_{i∈I} JH(Mᵢ)` in Lemma (iii). These later results are not formalized here; they are the reason for the specialization `w = max u v` recorded below.

The source gives no proof of the remark. The construction here is the standard one that the two definitions above suggest: the sum of a family `(Mᵢ)` is the image of the map `⊕ᵢ Mᵢ → M` induced by the inclusions, that is, the smallest subobject through which every inclusion factors.

Errata: no project errata note `notes/errata/renard-2026-representations-groupes-reductifs-padiques.md` exists in the published Library notes or the project notes. The snapshot of the author's page in `/home/taskhub/pilot/literature` (26 October 2026) links an erratum only for the 2010 edition; the retained 2010 correction list `renard-2010-corrections-complements` is supplementary; its Appendix A entries (PDF18–19) were read at authoring, and none concerns AB4\*, AB5 or sums of subobjects. No repair of the source is made.

## Universes and assumptions

Throughout, `C : Type u` carries `Category.{v} C`, and families are indexed by `I : Type w`. The universes `w`, `v` and `u` are independent, and every declaration lists its level parameters in the order `w, v, u`, as in `Langlands.CategoryTheory.RenardGrothendieckAxioms`.

The general construction and its laws assume only what the construction uses, for the one family `F : I → Subobject X` at hand:

- `[HasCoproduct fun i => (F i : C)]`: the coproduct of the underlying objects exists;
- `[HasImage (Sigma.desc fun i => (F i).arrow)]`: the coproduct map has an image.

No `WellPowered`, `LocallySmall`, generator, separator, Grothendieck, finiteness, exactness or complete-lattice assumption is made. In particular, Mathlib's `CategoryTheory.Subobject.sSup` (`Mathlib/CategoryTheory/Subobject/Lattice.lean`, section `Sup`) is not used: it indexes the coproduct by a small copy of an arbitrary set of subobjects and therefore assumes `LocallySmall.{w} C` and `WellPowered.{w} C`. Here the family is already indexed by `I : Type w`, so no reindexing is needed. No order or lattice instance is introduced; `≤`, `IsLUB` and `⊥` are Mathlib's existing ones on `Subobject X`.

## The construction and its representative maps

For `X : C`, `I : Type w` and `F : I → Subobject X`:

| Declaration | Type (instances as above) | Meaning |
| --- | --- | --- |
| `subobjectSumDesc F` (`abbrev`) | `(∐ fun i => (F i : C)) ⟶ X` | The coproduct map `Sigma.desc fun i => (F i).arrow`, whose restriction to the `i`-th summand is the inclusion of `F i`. |
| `subobjectSum F` (`def`) | `Subobject X` | `Subobject.mk (image.ι (Sigma.desc fun i => (F i).arrow))`: the subobject represented by the image inclusion of the coproduct map. |
| `subobjectSum_def F` | `subobjectSum F = Subobject.mk (image.ι (Sigma.desc fun i => (F i).arrow))` | The defining equation, by `rfl`. |
| `subobjectSumIso F` (`def`) | `(subobjectSum F : C) ≅ image (subobjectSumDesc F)` | The representative isomorphism `Subobject.underlyingIso` between the object underlying the sum and the actual image object. |
| `subobjectSumIso_hom_comp_image_ι F` | `(subobjectSumIso F).hom ≫ image.ι (subobjectSumDesc F) = (subobjectSum F).arrow` | Compatibility of the isomorphism with the inclusions (`simp`, `reassoc`). |
| `subobjectSumIso_inv_comp_arrow F` | `(subobjectSumIso F).inv ≫ (subobjectSum F).arrow = image.ι (subobjectSumDesc F)` | The inverse form (`simp`, `reassoc`). |
| `subobjectSumπ F` (`def`) | `(∐ fun i => (F i : C)) ⟶ (subobjectSum F : C)` | `factorThruImage (subobjectSumDesc F) ≫ (subobjectSumIso F).inv`, the map from the coproduct onto the sum. |
| `subobjectSumπ_arrow F` | `subobjectSumπ F ≫ (subobjectSum F).arrow = subobjectSumDesc F` | The coproduct map factors through the sum (`simp`, `reassoc`). |
| `epi_subobjectSumπ F` (instance) | `[HasEqualizers C] → Epi (subobjectSumπ F)` | With equalizers, the map onto the sum is an epimorphism, since `factorThruImage` is. |

The coproduct map, the image inclusion `image.ι (subobjectSumDesc F)` and the representative isomorphism are therefore all available by name for later canonical-map constructions. The sum is the actual image subobject, not an element chosen from a proof that a least upper bound exists.

## Intrinsic laws

Under the same two instance assumptions:

| Declaration | Statement |
| --- | --- |
| `le_subobjectSum F i` | `F i ≤ subobjectSum F` |
| `subobjectSum_le F h` | `(∀ i, F i ≤ G) → subobjectSum F ≤ G`, for `G : Subobject X` |
| `subobjectSum_le_iff F` | `subobjectSum F ≤ G ↔ ∀ i, F i ≤ G` |
| `isLUB_subobjectSum F` | `IsLUB (Set.range F) (subobjectSum F)` |
| `subobjectSum_eq_of_isLUB F hU` | `IsLUB (Set.range F) U → subobjectSum F = U` |

Proofs, as implemented:

- **Upper bound.** `Subobject.le_of_comm` reduces `F i ≤ subobjectSum F` to a morphism `(F i : C) ⟶ (subobjectSum F : C)` compatible with the arrows. The morphism is `Sigma.ι _ i ≫ subobjectSumπ F`. Compatibility is proved by `simp` with `subobjectSumπ_arrow` and `Sigma.ι_desc`: composing with the arrow of the sum gives `(F i).arrow`.
- **Least.** Given `h : ∀ i, F i ≤ G`, the maps `Subobject.ofLE (F i) G (h i)` assemble by `Sigma.desc` into a map `∐ (F i) ⟶ (G : C)`. Followed by the mono `G.arrow`, it gives the coproduct map, checked summand by summand (`ext`, then `simp` with `Subobject.ofLE_arrow`). This is a mono factorisation of the coproduct map through `G`, so `image.lift` gives `image (subobjectSumDesc F) ⟶ (G : C)` with `image.lift_fac`. Precomposed with `(subobjectSumIso F).hom`, it gives the morphism required by `Subobject.le_of_comm`. This is the image's universal property: the image is the smallest subobject through which the coproduct map factors.
- `subobjectSum_le_iff` combines the two directions with transitivity. `isLUB_subobjectSum` restates them for `Set.range F`. `subobjectSum_eq_of_isLUB` is uniqueness of least upper bounds in a partial order (`IsLUB.unique`).

The proofs follow the pattern of Mathlib's `Subobject.le_sSup` and `Subobject.sSup_le`, without the small reindexing.

## Existence theorems for `HasIndexedSubobjectSums`

`Langlands.Renard.HasIndexedSubobjectSums.{w} C` is the comparison predicate from `Langlands.CategoryTheory.RenardGrothendieckAxioms`: every `w`-indexed family of subobjects of every object, including the empty family, has a least upper bound. Its complete types, as checked:

```lean
Langlands.Renard.hasIndexedSubobjectSums_of_hasImages.{w, v, u} :
  ∀ {C : Type u} [inst : Category.{v, u} C] [HasImages.{v, u} C],
    HasCoproducts.{w, v, u} C → Langlands.Renard.HasIndexedSubobjectSums.{w, v, u} C

Langlands.Renard.hasIndexedSubobjectSums_of_hasCoproducts.{w, v, u} :
  ∀ {C : Type u} [inst : Category.{v, u} C] [Abelian.{v, u} C],
    HasCoproducts.{w, v, u} C → Langlands.Renard.HasIndexedSubobjectSums.{w, v, u} C

Langlands.Renard.IsSourceCocomplete.hasIndexedSubobjectSums.{w, v, u} :
  ∀ {C : Type u} [inst : Category.{v, u} C] [inst_1 : Abelian.{v, u} C],
    Langlands.Renard.IsSourceCocomplete.{w, v, u} C →
      Langlands.Renard.HasIndexedSubobjectSums.{w, v, u} C
```

Each takes the family `F` given by the predicate and supplies the witness `subobjectSum F` with `isLUB_subobjectSum F`. The first theorem is the generalization to categories with images. The second is the source-facing theorem: an abelian category satisfying source AB4\* at size `w`, which is `HasCoproducts.{w} C`, has sums of all `w`-indexed families of subobjects. The third states the same for the source term "cocomplete", the abbreviation `IsSourceCocomplete.{w} C` of `HasCoproducts.{w} C`. These theorems formalize the source remark and an intrinsic law of the concrete construction; they say nothing about AB5 distributivity.

`HasIndexedSubobjectSums.{w} C` concerns families indexed by `Type w`. It is not the same as existence of least upper bounds of all subsets of `Subobject X`: `Subobject X` lives in `Type (max u v)`, and when `w` is smaller, an arbitrary subset need not be indexed by a type in `Type w`.

## The source abelian specialization

In the section with `[Abelian C]` and `[HasCoproducts.{w} C]`:

- `subobjectSum_eq_mk F : subobjectSum F = Subobject.mk (image.ι (Sigma.desc fun i => (F i).arrow))`, proved by `rfl`. The right side is elaborated with the instances that `[Abelian C]` and `[HasCoproducts.{w} C]` provide, so the general definition, specialized, is literally this expression.
- `subobjectSum_eq_bot_of_isEmpty F : subobjectSum F = ⊥` for `[IsEmpty I]`. The range of an empty family is empty; a least upper bound of `∅` is a bottom element (`isLUB_empty_iff`), hence equals `⊥` (`IsBot.eq_bot`). Here `⊥` is Mathlib's `Subobject.orderBot`, the subobject `Subobject.mk (initial.to X)`; in an abelian category it is the zero subobject. The construction therefore covers the empty family, whose coproduct is an initial object.

## Specialization `w = max u v`

`isLUB_subobjectSum_set`:

```lean
Langlands.Renard.isLUB_subobjectSum_set.{v, u} :
  ∀ {C : Type u} [inst : Category.{v, u} C] [inst_1 : HasImages.{v, u} C]
    [inst_2 : HasCoproducts.{max u v, v, u} C] {X : C} (s : Set (Subobject.{v, u} X)),
    IsLUB s (Langlands.Renard.subobjectSum.{max u v, v, u} fun P => ↑P)
```

Since `Subobject X : Type (max u v)`, every set `s` of subobjects is indexed by its subtype, a type in `Type (max u v)`, with range `s`. Taking `w = max u v`, the sum of this family is a least upper bound of `s`. This is a legitimate instance of the general construction for later finite-type (source AB6) arguments that sum arbitrary sets of subobjects. It assumes coproducts indexed by `Type (max u v)`. It does not lower the size: obtaining least upper bounds of arbitrary sets from coproducts of a smaller size `w` would need a separate smallness argument, which is not made here.

## Scope and deferred obligations

Specified by Worker 6's task `5a53b608-497a-4bd9-9923-f0b0db212357`, successor of the definition unit `Langlands.CategoryTheory.RenardGrothendieckAxioms` (task `99601a3d-50ed-4a01-a5d7-0503d8ede01a`). The following remain separate obligations:

- the AB5 distributivity law itself, and comparisons of source AB5 with filtered-colimit exactness (Mathlib's `AB5OfSize`);
- source A.VI.2(10): complete or cocomplete abelian categories have all limits or colimits;
- locally finite type (source AB6, A.VI.3), finite length, the Jordan–Hölder theorem, composition-factor identities and semisimplicity.

The file contains no proof holes and no new axioms; the theorems depend only on `propext`, `Classical.choice` and `Quot.sound`.
