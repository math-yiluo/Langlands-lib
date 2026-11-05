# Renard all-open sheaves and Mathlib at the original section universe

This is an internal source correspondence for David Renard,
*Représentations des groupes réductifs p-adiques*, French version dated
9 July 2026. The source definitions are II.2.1, printed pp.33–34 /
PDF pp.39–40: normalized abelian-group presheaves on a chosen basis,
restriction-compatible morphisms (II.2.1.1), and unique gluing (F) with
compatibility on every smaller basis open in an overlap. A.VI.1, printed
p.261 / PDF p.267, lists abelian-group sheaves and presheaves on a
topological space among the abelian-category examples. The registered
source is `renard-2026-representations-groupes-reductifs-padiques`,
SHA256 `7b539996793b7c3620e72e1e389588eb42d1a8e91d6f68b2eead5c2e2ffc182c`.
These three PDF pages were read directly for this unit. The separately
registered historical 2010 errata, PDF pp.2–3, were also read; their later
sheafification corrections do not change these definitions.

The book does not state a comparison with Mathlib. The construction here
identifies the published source all-open category with Mathlib's actual
site sheaf category. All declarations are in
`Langlands.Sheaf.Renard.AllOpenMathlib`. The space has its supplied
topology, in universe `u`; original additive-group carriers stay in the
independent universe `v`. The returned equivalence is literally

```text
BasisSheaf.{u,v} (allOpenBasis X)
  ≌ TopCat.Sheaf AddCommGrpCat.{v} (TopCat.of X).
```

The arbitrary-topology scope agrees with the A.VI.1 example and documents
the extension beyond the t.d. setting of Chapter II. The actual II.2.1
opening definitions themselves start with a topological space and a basis.
Empty spaces, empty opens, and empty covers are included throughout.

`rawToMathlib` precomposes with the published
`LocallyConstantScalar.allOpenFunctor X` opposite. `rawFromMathlib`
precomposes with the published `basisInclusion (allOpenBasis X)` opposite.
Both maps on morphisms are the corresponding precompositions of the
original natural transformation. The `rawToMathlib_obj`,
`rawToMathlib_restriction`, and `rawToMathlib_map_app` laws identify the
forward sections, restrictions and morphism components with the original
ones at `allOpen U`. The three corresponding `rawFromMathlib` laws
identify the reverse data with the original Mathlib data at `op W.obj`.
The four `map_id` and `map_comp` laws expose their identity and composition
laws. No section group is replaced by a larger carrier. `allOpen_obj`
identifies `allOpen W.obj` with the original basis object, using structure
eta and proof irrelevance. `rawUnitIso` and `rawCounitIso` use identity
additive maps on those same groups; naturality follows from the category
identity laws and the original maps.

`compatible_iff` compares the literal source predicate with Mathlib's
pairwise-intersection compatibility on the underlying type-valued
presheaf. In the forward direction take the all-open object associated
to the intersection itself. In the reverse direction, restrict equality
on that intersection to the arbitrary smaller open, and use the existing
`restriction_comp_apply` law on both sides. Thus every smaller-overlap
test in the source condition is retained.

`uniqueGluing_of_sheafCondition` applies the published
`SheafCondition.family` to the cover of a family's union. Conversely,
`sheafCondition_of_uniqueGluing` applies type-valued unique gluing to the
membership subtype of the source set cover. Its union equals the
original covered open, by the two parts of `FamilyCovers`. The proof
transports the amalgamation along that equality, applies
`restriction_transport` for the restriction equations, and transports a
competing amalgamation back for uniqueness. This retains the original
set-cover encoding, including its empty cover.

`isSheaf_iff_underlying` uses the two separate Mathlib site theorems
`CategoryTheory.Presheaf.isSheaf_comp_of_isSheaf` and
`CategoryTheory.Presheaf.isSheaf_of_isSheaf_comp`. The existing
`forget AddCommGrpCat.{v}` instances preserve and reflect existing limits
at the necessary index sizes. Neither direction needs existence of all
such limits. Combining these with
`TopCat.Presheaf.isSheaf_iff_isSheafUniqueGluing_types` proves
`sheafCondition_iff` for every actual raw source presheaf and the actual
`Opens.grothendieckTopology (TopCat.of X)`. The stronger convenience
algebraic unique-gluing equivalence is not used. There are no `Small`,
`UnivLE`, `HasLimitsOfSize`, cardinality, or sheafification hypotheses.

`fromMathlib_sheafCondition` uses the raw counit to apply this comparison
to any actual Mathlib sheaf. `fromMathlib_isNormalized` then derives
normalization by the published empty-cover uniqueness argument
`SheafCondition.isNormalized`; normalization is not supplied as an input.
`fromMathlib_unique_gluing` exposes the resulting arbitrary-indexed
family gluing directly on the original Mathlib groups and restrictions.
Its index universe `w` is independent of both `u` and `v`, through the
published set-cover range/deduplication theorem `SheafCondition.family`.

`toMathlib` and `fromMathlib` lift the raw precompositions to the actual
bundled sheaf categories, preserving the two existing source
full-subcategory layers. Their section, restriction and morphism laws
are `toMathlib_sections`, `toMathlib_restriction`, `toMathlib_map_app`
and the corresponding `fromMathlib` laws. `toMathlib_forget` and
`fromMathlib_forget` are equalities with the actual `sheafForget`,
`presheafInclusion` and `TopCat.Sheaf.forget` composites, for objects
and original natural transformations together.

`unitIso` and `counitIso` lift the raw identity-section isomorphisms
through those same full subcategories. The four `unit_hom_raw`,
`unit_inv_raw`, `counit_hom_raw`, and `counit_inv_raw` laws identify
the actual underlying natural transformations. The four `*_app` laws
identify their additive maps as identities, and the four `*_apply`
laws evaluate them as `s ↦ s` on every original section. The source
formulas use the canonical identification `allOpen W.obj = W`; no
section-level isomorphism or universe lift is inserted. Naturality
in both directions is exposed by `unit_naturality`,
`unit_inv_naturality`, `counit_naturality`, and
`counit_inv_naturality`. The four `*_hom_inv_id` / `*_inv_hom_id`
laws expose the inverse identities in the actual sheaf categories.

`equivalence` uses exactly these two functors and these unit and counit.
Its required coherence equation follows by forgetting to the underlying
natural transformation and evaluating the identity maps.
`functor_triangle` exposes that law and `inverse_triangle` exposes the
other triangle law, derived from the actual equivalence. Consequently
the construction is suitable for subsequent categorical transport.

Worker 1594 implemented the construction and intrinsic laws. Worker 709
provided the task's original-source audit and the universe-safe route
through preservation and reflection of existing limits. Published
prerequisites are reused by Lean name, including the source basis
presheaf/sheaf categories and the existing all-open lift.

This unit proves no abelianness assertion. The arbitrary chosen-basis /
all-open equivalence, normalized-presheaf abelianness, actual sheaf
abelianness and its sheafification premises, original-universe germ
models, stalk comparisons, compact sections, and scalar or module
enhancements remain separate obligations. No separation, compactness,
countability, nonemptiness, or total-disconnectedness hypothesis is added.
