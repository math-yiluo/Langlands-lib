# The categorical universal property of the actual ring localization

Worker 709 prepared this statement pair. Worker 1301 contributed the
ring-denominator and factor interfaces and their proposed categorical
universal-property formulation. The file imports the published
`Langlands.Algebra.RenardLocalRingCategory`; its constructions are unchanged.
This unit states the property, whose proof remains a separate obligation.

## Source and provenance

The governing source is David Renard, *Représentations des groupes réductifs
p-adiques*, French version dated 9 July 2026, Appendix A.III.1, printed
pp.251–252 / one-based PDF257–258. PDF257 defines a right universal problem
by unique factorization. Example 3 on PDF258 applies it to commutative
unital rings with designated multiplicative subsets and their unital
ring maps preserving those subsets. The local full subcategory consists
of the pairs whose designated elements are units. The example asserts
that the actual localization and its natural map solve that problem,
including the zero-ring boundary when zero is designated.

The registered source is
`renard-2026-representations-groupes-reductifs-padiques`, SHA256
`7b539996793b7c3620e72e1e389588eb42d1a8e91d6f68b2eead5c2e2ffc182c`.
These original pages were read directly on 4 November 2026. The supplementary
older-edition source `renard-2010-corrections-complements`, SHA256
`fdf3c88716c294c451c1f6fad67f6b99c95dae670aae0b8ad191ab0a96e69863`,
was also checked directly on PDF18–19; those pages do not change example 3.
This bounded observation does not claim an exhaustive errata audit.

The named full subcategory, designated image submonoid, explicit chosen
factor and `StructuredArrow` presentation are internal derived formulations
of the source example. The source does not specify the localized pair's
designated submonoid or a carrier-universe convention. The statement retains
the published image choice and arbitrary common carrier universe.

## Actual objects and quantifiers

All declarations are in `Langlands.Renard.RingLocalization`. Each is a
closed `def` returning `Prop`; the carrier universe `u` is arbitrary.
`RingPair.{u}` has objects in `Type (u + 1)` with commutative unital ring
carriers in `Type u`, and its morphisms lie in `Type u`.

For every `A : RingPair.{u}`, the imported `canonicalLocalObject A` has
underlying ring `Localization A.denominators`. Its designated submonoid
is precisely the image of `A.denominators` under the actual `algebraMap`.
The locality of this object is already proved in the construction.
`canonicalRingMap A` is that algebra map regarded as a
denominator-preserving morphism.

The target `N : LocalRingCat.{u}` is arbitrary in the actual full
subcategory selected by `localRingProperty`. Its designated submonoid
may be any submonoid of its units. In particular it need not designate
all its units. An ambient `f : A ⟶ N.obj` is any unital ring map
preserving the designated submonoids. The actual local-category morphism
`canonicalFactor A N f` is the published `IsLocalization.lift`, with its
denominator-preservation law proved using witnesses in the designated
image. The inclusion retains all these ambient maps.

## Exact assertions

`CategoricalFactorizationStatement` universally quantifies over `A`, `N`
and `f` as above and asserts

```text
canonicalRingMap A ≫
  localRingInclusion.map (canonicalFactor A N f) = f.
```

Thus composition first takes the canonical map and then the image of the
constructed factor, in the direction of Renard's right universal problem.

`CategoricalFactorUniquenessStatement` also quantifies over every actual
local-category morphism `g : canonicalLocalObject A ⟶ N`. Assuming only

```text
canonicalRingMap A ≫ localRingInclusion.map g = f,
```

it concludes `g = canonicalFactor A N f`. Together with the preceding
clause this asserts existence and uniqueness for every `f`, identifying
the particular constructed factor.

`CategoricalInitialityStatement` universally quantifies over `A` and asserts

```text
Nonempty (StructuredArrow.IsUniversal (canonicalStructuredArrow A)).
```

In pinned Mathlib, `StructuredArrow.IsUniversal` abbreviates initiality
data for the actual structured arrow. `Nonempty` expresses the existence
of those data as a proposition. Initiality tests every structured arrow,
hence every actual local target and every map from `A`; no universal-property
certificate is assumed as input.

`CategoricalUniversalStatements.{u}` is the conjunction of these three
closed propositions. The first two clauses identify the chosen factor;
the third records initiality of the chosen arrow itself.

The ring may be the zero ring, and every denominator submonoid is allowed,
including those containing zero. In that boundary case the imported
construction already proves that the localized ring is subsingleton.
There is no nontriviality, domain, finiteness, dimension or `Small`
assumption. Source and target carriers use the same arbitrary `u` as
the ambient category; no independent-universe transport or shrinking is
asserted here.

## Proof obligation and remaining scope

An intended proof may use `canonicalFactor_algebraMap` for the factorization
equation, localization ring-map extensionality for uniqueness, and the
resulting unique factors to construct initiality in the actual
structured-arrow category. These are proposed steps only; this file
implements no proof of the three propositions.

The compatible-isomorphism comparison remark, a localization functor,
reflection or adjunction, independent-target-universe transport, the other
examples, and the rest of Appendix A retain their separate obligations.
This statement does not complete A.III or the whole-book program.
