# Renard's local finite-type condition and source AB6

This module defines local finite type for actual categorical objects and categories, and Renard's AB6 in the abelian context. It imports `Langlands.CategoryTheory.RenardFiniteType` unchanged. It also gives a sized comparison formulation and five short intrinsic order lemmas. All five predicates are transparent `def` or `abbrev` declarations returning `Prop`; none is a typeclass.

The governing source is David Renard, *Représentations des groupes réductifs p-adiques*, French edition dated 9 July 2026, A.VI.3, printed page 263 / PDF269. Registered literature ID: `renard-2026-representations-groupes-reductifs-padiques`, SHA256 `7b539996793b7c3620e72e1e389588eb42d1a8e91d6f68b2eead5c2e2ffc182c`, retained original `/home/taskhub/central-library/Renard--Representations des groupes reductifs p-adiques (2026 version)--2026.pdf`. PDF269–271 and the referenced A.I.3 PDF254–255 were read. PDF269 was rendered and visually inspected. After the pure Jordan–Hölder theorem, Renard separately assumes that the category is Grothendieck and introduces AB6: "tout objet de A est une somme de sous-objets de type fini" (every object of A is a sum of finite-type subobjects). Footnote 1 identifies this condition as local finite type and explicitly distinguishes it from Grothendieck's Tohoku AB6. The definition here follows that wording. The subsequent proofs on PDF270–271 use AB6 to obtain finite-type subobjects of a given object.

The finite-type predicate is the published `Langlands.Renard.IsFiniteTypeObject`. In particular, it includes existence of all subobject unions for the object and the nonempty proper-chain condition. Its paired Markdown documents the zero-object convention and the repairs to A.I.3. The current published `notes/renard/appendix-a-corrections.md` was consulted; it treats different passages. The supplementary registered 2010-edition errata, `renard-2010-corrections-complements`, SHA256 `fdf3c88716c294c451c1f6fad67f6b99c95dae670aae0b8ad191ab0a96e69863`, were consulted at PDF18–19. Their only nearby item, for 2010 page 305, replaces an increasing sequence by a chain in the Zorn argument of the subsequent proposition's proof; the 2026 text already uses chains, and no item concerns the AB6 definition. No dedicated `notes/errata/renard-2026-representations-groupes-reductifs-padiques.md` was found in the workspace, project or pinned Library. This does not assert that all possible later errata were found. No change to the AB6 passage or its footnote is proposed here.

## Canonical predicates

Throughout, `C : Type u` has `Category.{v} C`, with independent object and Hom universes. `Subobject X` is Mathlib's actual quotient of monomorphisms into `X` by isomorphism over `X`. Every least upper bound below uses its existing categorical order. The top subobject is the class of the identity of `X`.

`IsLocallyFiniteTypeObject X` is exactly

```lean
IsLUB {P : Subobject X | IsFiniteTypeObject (P : C)} (⊤ : Subobject X)
```

Here `(P : C)` is the actual domain object chosen by Mathlib's existing subobject coercion, `Subobject.underlying.obj P`. The predicate says that top is a least upper bound of the subset of finite-type subobjects. It asserts that the required sum exists and equals top, rather than being conditional on existence of a sum. No complete-lattice instance is chosen.

`IsLocallyFiniteTypeCategory C` says that every `X : C` satisfies this object predicate. These two definitions need only actual category data: this is an intrinsic extension of the source formulation beyond abelian categories. `SourceAB6 C` is an alias for the category predicate with actual `[Abelian C]` explicitly required in its full type, `(C : Type u) → [Category.{v} C] → [Abelian C] → Prop`, retaining the source context.

The source's separate Grothendieck hypothesis is not a conjunct of `SourceAB6`. Dependent source results must state it separately, using the published `IsSourceGrothendieck.{w} C` with a justified family size. No generator, separator, Noetherianity, finite presentability, `WellPowered` or `LocallySmall` condition is included.

## Sized comparison

For an independent universe `w`, `IsLocallyFiniteTypeObjectOfSize.{w} X` is

```lean
∃ (I : Type w) (F : I → Subobject X),
  (∀ i : I, IsFiniteTypeObject (F i : C)) ∧
    IsLUB (Set.range F) (⊤ : Subobject X)
```

`IsLocallyFiniteTypeCategoryOfSize.{w} C` requires this for every object. These definitions record an explicit covering-family size, and carry `@[pp_with_univ]` so that the size is printed. No `Nonempty I` is imposed, so an empty cover is permitted when top is also the least subobject, as for a zero object in an abelian category. The predicates do not themselves assert that a zero object is finite type or construct such a cover. Repeated members of a family do not change its range or its least upper bound.

Mathlib's actual `Subobject X` lies in `Type (max u v)`. The canonical predicates are equivalent to the sized predicates at this bound. No equivalence at an arbitrary smaller `w` and no shrinking theorem is claimed.

## Intrinsic comparison lemmas

These order lemmas are internal consequences of the definitions, explaining the canonical translation of the source's unspecified covering family. They do not prove a further substantive source theorem.

`IsLocallyFiniteTypeObjectOfSize.isLocallyFiniteTypeObject` takes a sized finite-type covering family. Top bounds every subobject. If `Q` bounds all finite-type subobjects, it bounds every member of this covering family. The family's least-upper-bound property then gives `⊤ ≤ Q`. Thus top is least for the full subset of finite-type subobjects. The proof works for every family universe `w`.

`IsLocallyFiniteTypeObject.ofSize` takes the canonical predicate. It uses the subtype `{P : Subobject X // IsFiniteTypeObject (P : C)}` as the index type and the subtype-value map as the family. The range of this map is proved equal to the full finite-type subset by explicit witnesses in both directions. Rewriting by that equality transports the supplied least-upper-bound proof. The subtype lies in `Type (max u v)`, so this comparison makes no assumption that the actual subobject type is smaller. No representatives of isomorphism classes are chosen beyond Mathlib's existing subobject coercion.

`isLocallyFiniteTypeObject_iff_ofSize` combines the two implications at the bound `max u v`:

```lean
IsLocallyFiniteTypeObject X ↔ IsLocallyFiniteTypeObjectOfSize.{max u v} X
```

`IsLocallyFiniteTypeCategoryOfSize.isLocallyFiniteTypeCategory` applies the first object lemma to every object, at any family universe `w`. `isLocallyFiniteTypeCategory_iff_ofSize` applies both object lemmas objectwise:

```lean
IsLocallyFiniteTypeCategory C ↔ IsLocallyFiniteTypeCategoryOfSize.{max u v} C
```

The implemented proofs use only upper-bound reasoning and the subtype range equality; they require no categorical sum construction, no choice of a smaller skeleton and no new axioms.

## Scope and provenance

This unit supplies neither the pure Jordan–Hölder theorem nor simple quotients, composition-factor identities, semisimplicity, finite-type/finite-cover comparisons, module finite-generation comparisons or finite-presentability/Grothendieck comparisons. Those remain separate statement/proof obligations.

The five predicates translate the cited source definition. The sized predicates and the five lemmas are internal comparison material requested by the task specification. Worker 6 prepared the initial paired draft. Worker 827 rechecked it against the source, added the two category-level lemmas and checked every complete declaration type.
