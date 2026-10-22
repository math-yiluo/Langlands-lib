# The right adjoint of étale restriction

For an étale morphism `f : Y ⟶ X` of Mathlib schemes, this module constructs
`directImage f A`, right adjoint to the published `restriction f A`. The namespace
is `Langlands.Geometry.EtalePullback`. The schemes use universe `u`, their small
étale sites have objects in `Type (u + 1)` and morphisms in `Type u`, and `A` is
an arbitrary category with independent object and morphism universes. No limits,
colimits, additive structure or sheafification in `A` are assumed.

## Constructing the required limits

`siteMapPullbackAdjunction` is Mathlib's actual adjunction between composition of
étale structure maps and base change along `f`. The left adjoint is the published
`siteMap f`; the right adjoint is `MorphismProperty.Over.pullback (@Etale) ⊤ f`.
Scheme pullbacks exist and étale morphisms are stable under base change.

Taking opposite categories makes `(siteMap f).op` a right adjoint. Each category
`StructuredArrow U (siteMap f).op` therefore has an initial object, recorded by
`rightComma_hasInitial`. This object is given by the unit of the opposite
adjunction. A limit over a category with an initial object is computed by
evaluation at that object. Thus every presheaf `F : Y.Etaleᵒᵖ ⥤ A` has a
pointwise right Kan extension along `(siteMap f).op`, recorded explicitly by
`hasPointwiseRightKanExtension`.

This proves existence of the particular limits needed for Kan extension even
when the site categories are larger than `A`; it does not assume all limits of
that size in `A`.

## Direct image and its adjunction

`directImage f A` is the functor induced by right Kan extension on presheaves:

```text
Sheaf(Y_et, A) → Presheaf(Y_et, A) → Presheaf(X_et, A).
```

The result is a sheaf because `siteMap f` is cocontinuous, as proved in
`EtalePullback`. The construction uses Mathlib's
`Functor.sheafPushforwardCocontinuous`. Its restriction to sheaves, together with
the continuity of the same site map, supplies `restrictionAdjunction`:

```text
restriction f A ⊣ directImage f A.
```

Consequently `restriction_preservesColimits` states preservation of every
colimit that exists, and `directImage_preservesLimits` states preservation of
every limit that exists. These preservation claims do not assert that arbitrary
`A`-valued sheaf categories have all such limits or colimits.

## Scope and provenance

This is internal categorical infrastructure for scheme étale cohomology, using
the published `EtalePullback` interface and Mathlib at commit
`5ed2965256430c3649e86755f9576b54eca72435`. Its inputs are the actual constructions
in `CategoryTheory/MorphismProperty/OverAdjunction.lean`,
`CategoryTheory/Adjunction/Opposites.lean`, `CategoryTheory/Adjunction/Comma.lean`,
`CategoryTheory/Limits/Shapes/Terminal.lean`, and
`CategoryTheory/Sites/CoverLifting.lean`. The proof route first establishes the
initial-object criterion and then applies the continuous/cocontinuous sheaf
adjunction. It does not assume the desired right adjoint as input.

Maps on derived global sections, compatibility with identity and composition
on cohomology, general non-étale morphisms, analytic sites, compact supports, and
the Harris Shimura/Hecke specialization remain separate constructions. No named
Harris or Berkovich theorem is asserted here.
