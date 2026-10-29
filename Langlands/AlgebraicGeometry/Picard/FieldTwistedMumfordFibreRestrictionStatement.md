# Both field fibre restrictions of a twisted ordinary Mumford tensor

`Langlands.AbelianScheme.FieldTwistedMumfordFibreRestrictionStatement.{u}`
is a `Prop`-valued definition stating two isomorphisms of actual line
bundles. It supplies a statement target, with no proof or new axiom.
Its provenance is an internal tensor generalization of the two displayed
restrictions in the proof of Edixhoven, van der Geer and Moonen,
*Abelian Varieties*, Proposition (7.21), printed p.106 / PDF p.110.

## Exact statement and constructions

For every `preservation : pullbackTensorComparisonIsIsoStatement.{u}`,
every field `K : Type u`, every
`A : AbelianScheme (Spec (CommRingCat.of K))`, and arbitrary
`L N R : LineBundle A.X.left`, put

```text
Z  := pullback A.X.hom A.X.hom
p1 := pullback.fst A.X.hom A.X.hom
p2 := pullback.snd A.X.hom A.X.hom
m  := Langlands.AbelianScheme.mumfordAddition A
Q  := (((m^*L tensor p1^*N) tensor p2^*N) tensor p2^*R).
```

Every pullback here is `LineBundle.pullback` and every tensor is
`LineBundle.tensor preservation`. In particular, the parentheses are
part of the actual expression. Its first three factors agree with the
ordinary expression in `mumfordBundle_forget`; the last factor is the
second-projection twist. `Q`, the projections and the maps below are
local lets, with no new public bundle or fibre-map definition.

For every rational point
`x : Over.mk (𝟙 (Spec (CommRingCat.of K))) ⟶ A.X`, define

```text
i1 := pullback.lift (A.X.hom ≫ x.left) (𝟙 A.X.left) (...)
i2 := pullback.lift (𝟙 A.X.left) (A.X.hom ≫ x.left) (...)
D  := LineBundle.tensor preservation
        ((LineBundle.pullback
          (Langlands.GroupScheme.translation A.toGrp x).left).obj L) N.
```

The compatibility proofs in both lifts use the over-section equation
`Over.w x`, namely `x.left ≫ A.X.hom = 𝟙 (Spec K)`. Thus `i1` has
coordinates `(x, id)` and `i2` has coordinates `(id, x)` on the actual
scheme fibre product. The full conclusion, for every `x`, is

```text
Nonempty ((LineBundle.pullback i1).obj Q ≅
  LineBundle.tensor preservation D R)
∧
Nonempty ((LineBundle.pullback i2).obj Q ≅ D).
```

An isomorphism is in the category `LineBundle A.X.left`, the full
subcategory of actual locally free rank-one sheaves of modules. These
conclusions therefore assert actual bundle isomorphisms, rather than an
equality of classes or an unspecified comparison certificate.

The only supplied mathematical parameter besides the field, abelian
scheme and line bundles is `preservation`. It is the published proposition
asserting that the canonical sheaf pullback/tensor comparison is an
isomorphism for every scheme morphism. The actual tensor construction
uses it to establish local rank one. No field-triviality, inverse
evaluation, rigidification, ampleness or translation-invariance hypothesis
is present.

## Source correspondence and the derived generalization

The registered original is B. Edixhoven, G. van der Geer and B. Moonen,
*Abelian Varieties*, preliminary version of the first chapters, source
`edixhoven-vandergeer-moonen-abelian-varieties-draft`, SHA256
`81e88e484e1e830286ffed93d4636c80e50a1c341ffe19cc198bd856be713b42`,
retained at
`literature/Edixhoven, van der Geer, Moonen - Abelian Varieties (preliminary version of the first chapters).pdf`.
The source proof begins on printed p.106 / PDF p.110, after the
proposition statement on printed p.105 / PDF p.109. Both pages were read
on 29 October 2026, and the restriction display on PDF p.110 was checked
visually.

The source takes `𝒦 = Λ(L) ⊗ p₂^*M⁻¹` and displays

```text
𝒦|_{ {x} × X } ≅ t_x^*L ⊗ L⁻¹ ⊗ M⁻¹,
𝒦|_{ X × {x} } ≅ t_x^*L ⊗ L⁻¹.
```

In the intended application, `N` is a supplied inverse of `L`, `P` is
the source's invariant bundle `M`, and `R` is a chosen inverse of `P`.
Then `Q` is precisely the ordinary tensor expression
`Λ(L) tensor p2^*R`, with the displayed parentheses. The restriction
calculation itself never uses either inverse evaluation, so the present
statement allows arbitrary `N` and `R`. It also needs no rigidification
on `L`. This strengthening is derived from the tensor calculation; it
is not attributed as the literal scope of Proposition (7.21).

The Library's translation is left translation, `y ↦ x * y`. Along `i1`,
addition is this translation directly. Along `i2`, addition is
`y ↦ y * x`; commutativity of the actual abelian scheme identifies it with
the same `GroupScheme.translation A.toGrp x`. No translation-invariance
property of a bundle is involved.

## Constant factors and the later proof obligation

Writing `c_x = A.X.hom ≫ x.left`, pulling back the four displayed
factors before removing constants gives

```text
i1^*Q ≅ (((t_x^*L tensor c_x^*N) tensor N) tensor R),
i2^*Q ≅ (((t_x^*L tensor N) tensor c_x^*N) tensor c_x^*R).
```

The factors `c_x^*N` and `c_x^*R` are pulled back from the line bundles
`x^*N` and `x^*R` on `Spec K`. The published unconditional theorem
`Langlands.AlgebraicGeometry.Picard.fieldLineBundleTriviality` identifies
their underlying modules with the structure sheaf; pulling back these
isomorphisms and using the tensor unitors removes all the constant
factors. The isomorphisms need not be canonical. `Nonempty` expresses the
required existence without choosing a scalar trivialization in the
statement.

The source assumes an algebraically closed field for the surrounding
lifting argument. This restriction computation extends to every field
using the same unconditional triviality theorem on `Spec K`. It retains
arbitrary universe, characteristic and dimension zero. It requires no
cube theorem, cohomology, Picard or dual representability, chosen-dual
surjection, or lifting theorem.

A later exact-target proof must prove the entire named proposition,
with no additional outer hypotheses. The published
`MumfordPicardZero.pullbackTensorIso`, `pullbackCompIso`, `tensorIsoOf`
and `constantIso`, together with the actual pullback coordinate
identities and the group-law identities, provide the intended route.
The scalar triviality premise of `constantIso` must be supplied by
`fieldLineBundleTriviality`, not retained as a new hypothesis. This
statement module does not discharge that proof obligation.

## Errata check and scope

On 29 October 2026, the registered PDF hash was verified and the current
published notes and retained literature filenames were searched for
source-specific errata. No errata note for this source was present in
those checked locations. This records the local check, rather than
asserting that no errata exist elsewhere.

Later on printed p.106 the draft cites Lemma (7.15) for a cohomological
support assertion; the surrounding argument appears to use (7.19)
together with (7.20). The two displayed restrictions precede that step
and do not depend on it. The present statement makes no assertion about
that support calculation or the conclusion of Proposition (7.21).

Worker 5 implemented the pair. Worker 516 supplied the precise
specification and the source and reuse map.
