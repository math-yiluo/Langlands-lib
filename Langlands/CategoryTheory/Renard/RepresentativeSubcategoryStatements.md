# Renard A.II.2: equivalence with the full representative subcategory

`Langlands.Renard.RepresentativeSubcategoryEquivalenceStatement C` states
that the actual inclusion of the full subcategory of chosen representatives
admits one reverse functor and both natural isomorphisms. It is a
proposition definition, with no proof in this pair.

## Governing source

The source is David Renard, *Représentations des groupes réductifs p-adiques*,
French version dated 9 July 2026, registered as
`renard-2026-representations-groupes-reductifs-padiques`, SHA256
`7b539996793b7c3620e72e1e389588eb42d1a8e91d6f68b2eead5c2e2ffc182c`.
The original A.II.2 introduction, printed pp.250–251 / PDF256–257,
was read, together with the quasi-inverse definition and final sufficient
criterion on PDF257; that page was also inspected visually. The introduction
chooses one object from every isomorphism class, keeps all morphisms
between selected objects, and motivates the equivalence of this category
with the original category.

The source's boxed quasi-inverse definition exchanges the identity-category
subscripts. This statement uses the already documented typed correction
from the [general criterion](EquivalenceCriterionStatements.md):
for an inclusion `ι : RepresentativeSubcategory C ⥤ C` and
`G : C ⥤ RepresentativeSubcategory C`, the isomorphisms are

```text
ι ⋙ G ≅ 𝟭 (RepresentativeSubcategory C),     G ⋙ ι ≅ 𝟭 C.
```

Lean writes composition in application order. Conventional `Gι` acts on
the representative category, and `ιG` acts on `C`. The strict-inverse
paragraph just before the boxed definition and A.I.1, printed p.247 /
PDF253, confirm this typing; these original passages were read during
the general criterion comparison. No source-specific Renard errata file
was found in the current published or project `notes/errata` locations.

## Exact target and actual objects

The imported [construction pair](RepresentativeSubcategory.md) defines
`representativeObjects C` as the actual ambient-object range of Mathlib's
`fromSkeleton C`. `RepresentativeSubcategory C` is the actual
`ObjectProperty.FullSubcategory` on this range, and
`representativeInclusion C` is its canonical inclusion. Thus this
statement refers to a constructed full subcategory, rather than an
arbitrary full subcategory assumed to have the desired properties.
The construction also gives a representative and actual isomorphism
for each ambient object, and proves equality of isomorphic selected objects.

The existential quantifier binds a single actual reverse functor `G`.
Both conjuncts use that same functor. Each `Nonempty` wraps an actual
isomorphism in the corresponding functor category, so it includes
natural transformations, naturality and their inverse laws. Objectwise
isomorphisms alone do not satisfy the target. No triangle identity or
strict equality of composed functors is imposed.

The categories have independent object and Hom universes:
`C : Type u` with `[Category.{v} C]`; its constructed full subcategory
has object universe `u` and Hom universe `v`. There is no nonemptiness,
smallness, finiteness, additive or abelian premise. In particular the
statement includes the empty category and performs no universe shrinking.

## Scope and proof boundary

This comparison makes precise the representative-subcategory discussion
using one actual selection of representatives. It does not assert uniqueness
of a quasi-inverse, prescribe its action on objects, or assert a strict
inverse. A proof can apply the published general equivalence criterion
to the actual inclusion: fullness and faithfulness are intrinsic to the
full subcategory, and each ambient object has the isomorphism supplied
by `representativeIso`. This is a proof route, not a proof in this file.

The fixed-dimension vector-space example and remaining A.I–A.II assertions
retain their separate obligations. No section or whole-book completion is
claimed.
