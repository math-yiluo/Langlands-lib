# Equivariant bounded atlases on induced affinoid spectra

Author: Worker 56.

This module constructs the full-group action by actual bounded morphisms
of the quotient atlas built in [InducedAction](InducedAction.md), and lifts
the functor of [InducedFunctor](InducedFunctor.md) to equivariant atlas
presentations. Equivariance holds as equality of the entire bounded
atlas maps, including their algebra pullbacks.

The namespace is
`Langlands.Analytic.PresentedAffinoidAlgebra.InducedAction`.

## Inputs and retained geometry

Let `K : Type u` be a complete normed field with ultrametric distance,
`G : Type v` a topological group, and `H : Subgroup G` an open subgroup,
with `hH : IsOpen (H : Set G)`.
An input `X : NormContinuousSpace K H` is in the geometric opposite
of the published category of norm-continuous actions on actual finite
positive-polyradius quotient algebras. Write `A_X = X.unop.obj.V`.
For a geometric arrow `f : X ⟶ Y`, its retained original bounded map is
`f* : A_Y → A_X`.

`atlasPresentation H hH X` is the existing actual balanced spectrum
quotient, with its already constructed affinoid atlas. The underlying
space is `Spectrum H X.unop = G ×_H LocalSpectrum H X.unop` with the
original product-quotient topology. The chart algebras are precisely
`A_X`, and indices are cosets with nonempty original spectrum.

No further nonemptiness, finite-index, radius-one, reducedness,
local compactness or separation assumption is added. Empty spectra
have no charts, as in the imported construction. The base spaces lie
in universe `max u v`, and the chart indices in universe `v`.
No new atlas or topology is supplied as input.

## Full-group bounded atlas maps

For `g : G`, `strongActionMap H hH X g` bundles the actual continuous
map `z ↦ g • z` with bounded pullbacks for every chart pair whose target
contains that image. It uses the existing `chartTarget` for target
existence, `chartPullback` for the bounded algebra maps,
`chartPullback_chart` for their spectral realization, and
`chartPullback_naturality` for compatibility with both atlas
restrictions. Its type is `AffinoidAtlasPresentation.StrongHom`.

`atlasActionMap H hH X g` chooses the translated target chart for each
source chart. At a coset `c`, its pullback is the original bounded
inverse subgroup operator

`(X.unop.actionAut (correction H g c.val)).inv`.

The source and target algebras are both the retained `A_X`.
The base map is the actual quotient action. The chosen index is the
existing `chartTarget H X.unop hH g c`. Monotonicity follows because
containment between two nonempty disjoint source charts forces their
indices to agree. The chart equation is the previously proved action
realization formula. Restriction compatibility is the chosen-target
case of `chartPullback_naturality`.

`atlasActionMap_one` proves that the identity group element gives the
categorical identity of the actual atlas presentation. It checks the
base-map identity, the translated chart identity and the bounded
pullback identity. `atlasActionMap_mul` similarly proves

`atlasActionMap (g*k) = atlasActionMap k ≫ atlasActionMap g`.

The base-map equation is the quotient action law, the index equation
is `chartTarget_mul`, and the algebra equation is `pullback_mul`.
This order agrees with categorical endomorphism multiplication and
contravariant bounded pullbacks.

`atlasAction H hH X` packages the result as

```
Action (AffinoidAtlasPresentation.{u, max u v, v} K) G.
```

`atlasAutomorphisms H hH X` obtains its homomorphism into bounded
atlas automorphisms from Mathlib's `ρAut`. Thus inverses come from the
proved group laws; no bounded inverse existence theorem is assumed.

## Equivariant induction functor

`atlasMap_equivariant` proves, for every original geometric equivariant
bounded arrow `f : X ⟶ Y` and every `g : G`,

`atlasActionMap X g ≫ atlasMap f = atlasMap f ≫ atlasActionMap Y g`.

Equality of base maps is `balancedMap_equivariant`. Equality of chart
indices follows because the map retains each coset while the action
translates it. Equality of the bounded pullbacks is proved directly
on the original algebras: equivariance of `f*` at the inverse of
`correction H g c.val` gives the required equality of operators.
Agreement of spectral points is not used to identify these algebra
maps, so nilpotent information is retained.

`equivariantAtlasFunctor` has type

```
NormContinuousSpace K H ⥤
  Action (AffinoidAtlasPresentation.{u, max u v, v} K) G.
```

Its object map is `atlasAction`, and its arrow map is the existing
bounded `atlasMap` together with this equivariance proof. The existing
atlas-map identity and composition laws give its functor laws.
`equivariantAtlasFunctor_forget` states that forgetting the full-group
action recovers exactly `atlasFunctor H hH`.

`continuousAtlasFunctor` applies the actual base-space functor to
these categorical actions and lifts them to `ContAction TopCat G`.
Joint continuity is the already proved joint continuity of the quotient
action. This continuous realization satisfies

`continuousAtlasFunctor H hH = balancedFunctor H`.

The theorem `continuousAtlasFunctor_eq_balancedFunctor` is proved by
reflexivity: the constructions retain the same underlying quotient,
point action and continuous maps. Consequently the natural equivariant
spectrum comparison from `InducedFunctor` also compares spectrum
realization with the continuous realization of these bounded atlas
actions.

## Provenance and remaining obligations

The original motivation is Berkovich's unfinished *Etale equivariant
sheaves on p-adic analytic spaces* (1995–1996), Construction 1.1.2,
printed/PDF page 2. That construction forms copies indexed by `G/H`
and acts between them using the subgroup element determined by
`g*g_i = g_j*h`. The bounded atlas action here packages the existing
actual affinoid implementation of precisely that representative
action. The original page was read directly.

Registered original:
`provided-7bb3903652336bd799aad8853b8efd7ff3bcc0c7652745417f4745a14ac08e90`;
folder SHA256
`e046cadfb9dcec4b0cf6624f80d6316bf532416153b82023f5100bd1ab0726cd`;
member
`Berkovich--Etale equivariant sheaves on p-adic analytic spaces (unfinished manuscript)--1996.pdf`;
member SHA256
`91567a75866a27cbe6690b6f075693df5afaa02524223d94d52ea37d77bb6637`.

This is an internal derived construction using the actual quotient
atlas, bounded correction pullbacks and their algebraic laws from
`GeneralizedAffinoid.InducedAction`, the bounded functor and continuous
maps from `GeneralizedAffinoid.InducedFunctor`, the chosen and strong
atlas-map interfaces, and Mathlib's categorical actions.
It assumes none of the output action, action inverses or equivariance
equations that it constructs.

The result is a full-group action in the concrete category of supplied
atlas presentations, with joint continuity on its realized quotient
space. It does not identify norm-orbit continuity with Berkovich's
topology on analytic automorphisms, pass to an extended analytic atlas,
construct arbitrary overlapping-atlas induction, or establish the
analytic extension universal property of Construction 1.1.2.
Etale and quasi-etale sites and the Harris specialization remain
separate obligations.
