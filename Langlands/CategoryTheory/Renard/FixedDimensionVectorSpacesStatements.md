# Renard A.II.2: the fixed-dimension vector-space equivalence

`Langlands.Renard.FixedDimensionVectorSpaceEquivalenceStatement k n`
states that the actual inclusion of the one-object coordinate category
into the category of dimension-`n` vector spaces admits a quasi-inverse.
This pair defines the proposition; its proof is a separate obligation.

## Governing source

The source is David Renard, *Représentations des groupes réductifs p-adiques*,
French version dated 9 July 2026, registered as
`renard-2026-representations-groupes-reductifs-padiques`, SHA256
`7b539996793b7c3620e72e1e389588eb42d1a8e91d6f68b2eead5c2e2ffc182c`.
The original A.II.2 example and its following paragraph, printed p.251 /
PDF257, were read and the page was inspected visually. The example uses
all linear maps between vector spaces of one fixed dimension `n`, and
all linear endomorphisms of `kⁿ` in the one-object category. It states
that the inclusion is an equivalence. The following paragraph explains
the choice of an identification with `kⁿ` for each object.

The source's boxed quasi-inverse definition on this page exchanges
the identity-category subscripts. This pair uses the typed correction
documented in the [general equivalence criterion](EquivalenceCriterionStatements.md):
for `F : C ⥤ D` and `G : D ⥤ C`, Lean's application-order composition
gives `F ⋙ G ≅ 𝟭 C` and `G ⋙ F ≅ 𝟭 D`.

## Actual categories and exact conclusion

The imported [construction pair](FixedDimensionVectorSpaces.md) defines
`FixedDimensionVectorSpaces k n` as the full subcategory of actual
`ModuleCat k` objects satisfying both `FiniteDimensional k X` and
`Module.finrank k X = n`. The explicit finite-dimensionality condition
keeps the meaning correct at `n = 0`, since finrank alone can vanish
for infinite-dimensional spaces.

Its coordinate object is the actual lifted vector space
`ULift.{v} (Fin n → k)`, a universe copy of `kⁿ`.
`OneObjectVectorSpaceCategory k n` is the full singleton subcategory on
that object, retaining every linear endomorphism, including noninvertible
ones. `fixedDimensionVectorSpaceInclusion k n` is the actual canonical
inclusion of this full subcategory.

The statement binds one actual reverse functor

```text
G : FixedDimensionVectorSpaces k n ⥤ OneObjectVectorSpaceCategory k n.
```

Both conjuncts use that same `G`. They require actual natural isomorphisms
from the inclusion followed by `G` to the identity on the one-object
category, and from `G` followed by the inclusion to the identity on the
fixed-dimension category. Each `Nonempty` wraps an isomorphism in the
corresponding functor category, including naturality and inverse laws.
Objectwise isomorphisms alone do not satisfy the statement.

The field universe `u` and additional carrier-universe parameter `v`
are independent; carriers lie in `Type (max u v)`, as in the imported
construction. The only parameters are a field `k` and a natural number
`n`. There is no positivity, characteristic, cardinality or extra
finite-dimensionality premise, and the statement includes `n = 0`.

## Proof boundary

A proof may apply the published general equivalence criterion to the
actual inclusion. Its full-subcategory construction supplies fullness
and faithfulness, and `coordinateVectorSpaceIso k n X` supplies an
actual isomorphism from the image of the distinguished object to every
object `X`. This describes an available proof route, not a proof in
this pair.

The proposition imposes no strict inverse or uniqueness condition on
`G`, and no triangle identity beyond the source's quasi-inverse
condition. It addresses one fixed dimension at a time. Remaining
A.I–A.II assertions and the whole-book completion conditions retain
their separate obligations.
