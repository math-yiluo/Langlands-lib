# Exact restriction between slice sites

This is an internal categorical construction supporting source changes for
coefficient systems. It derives preservation and coherence from Mathlib's
existing slice-site functors; it asserts no new result from Harris or Berkovich.

## Inputs and direction

Let `C : Type uC` have hom universe `vC`, let `J` be a Grothendieck topology
on `C`, and let `A : Type uA` have hom universe `vA`. For an actual morphism
`f : X ⟶ Y`, Mathlib supplies

```text
J.overMapPullback A f : Sheaf (J.over Y) A ⥤ Sheaf (J.over X) A.
```

It precomposes presheaves with `(Over.map f).op`. Thus a sheaf on the slice
over `Y` is evaluated at the composite `U → X → Y`. This file uses precisely
that existing functor, with the topologies induced by `J` on both slices.

## Preservation

`overMapPullback_preservesLimitsOfShape` proves preservation of a shape
`K : Type uK` with hom universe `vK`, assuming `A` has limits of that shape.
It identifies the underlying presheaf functor with precomposition and uses
reflection of limits by `sheafToPresheaf`. This needs no products or
pullbacks in `C`.

`overMapPullback_preservesFiniteLimits` packages the result when `A` has
finite limits.

With `HasPullbacks C`, `overMapPullback_preservesColimitsOfSize` proves
preservation of colimits indexed by any category with object universe `uK`
and hom universe `vK`. The adjunction `Over.mapPullbackAdj f` induces an
adjunction on sheaves because Mathlib proves continuity of both site
functors. The restriction in question is its left adjoint. This assertion
does not require the sheaf categories to have all such colimits. Together,
these results give finite exactness whenever the categories involved are
abelian and the coefficient category has finite limits.

## Comparison with global restriction

`overPullbackMapIso` is the natural isomorphism

```text
J.overPullback A Y ⋙ J.overMapPullback A f ≅ J.overPullback A X.
```

It assembles Mathlib's `Sheaf.pushforwardOverMapIso`, which identifies both
sides on the same original sheaf. At every slice object `U → X`, both sides
are the original sheaf's value on `U`, and both the forward and inverse
comparison maps are identity maps. The two component lemmas record this.
Naturality follows from those identities.

`overPullbackMapIso_id` identifies this comparison with Mathlib's
`overMapPullbackId` after the functor right unitor.
`overPullbackMapIso_comp` identifies the direct comparison for `f ≫ g`
with the successive comparisons for `g` and `f`, using Mathlib's
`overMapPullbackComp` and the functor associator. Both proofs check
components on the underlying presheaves, where all comparisons are
identities.

## Provenance and limits

The implementation reuses the original pinned Mathlib modules
`CategoryTheory/Sites/Over.lean`, `Sites/Continuous.lean`, `Sites/Limits.lean`
and the preservation machinery imported by `Langlands.Sheaf.SliceExact`.
The preservation proofs follow the same underlying-presheaf argument as
`SliceExact` and the actual `Over.map ⊣ Over.pullback` adjunction. The
coherence statements derive from the explicit identity components of
Mathlib's slice comparisons.

No covering, torsor, conservativity, geometric base-change theorem,
cohomology comparison, or identification with a separately presented site
is claimed here.
