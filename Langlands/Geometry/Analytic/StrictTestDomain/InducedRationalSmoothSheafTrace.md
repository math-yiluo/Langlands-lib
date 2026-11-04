# Smooth coefficient sheaf trace on actual induced rational spectra

This module constructs smooth direct images, coefficient pullbacks and finite
covering traces along the original induced rational transport maps. It retains
the full locally constant coefficient sheaves and every original smooth
coefficient intertwiner. It proves the evaluation, degree, naturality, identity
and composition laws using the actual smooth direct-image comparisons.

The namespace is
`Langlands.Analytic.StrictTestDomain.RationalAutomorphism.RationalSpectralAction.OpenSubgroupTransport.SmoothSheafVariation`.

## Internal provenance and actual inputs

The construction specializes `Sheaf.Equivariant.SmoothDirectImage`, its
`Coefficients` and `CoveringTrace` modules, and the rational coefficient functor
in `InducedRationalSmoothSpatialSheaves`. Its comparison with the full trace
uses `InducedRationalSheafTrace`. These existing constructions supply the
smooth coreflection, ordinary covering-chart trace and all their intrinsic
laws. The new rational comparison laws transport those laws by the proved
equalities of the original rational continuous maps. No external literature
assertion or assumed trace compatibility is introduced.

All carriers share one arbitrary universe `u`, as required by the existing
smooth direct-image API. Let `K : Type u` be a complete normed ultrametric
field, `P` a presented strict affinoid algebra over it, `G : Type u` a
topological group, and `ρ : RationalSpectralAction G P`. Each object
`X : ρ.OpenSubgroupTransport` supplies its original open subgroup `H`, rational
quotient algebra, local Banach spectrum `X.LocalSpectrum`, and balanced induced
space `X.InducedSpectrum = G ×_H X.LocalSpectrum`. Their topologies and
continuous actions are the existing constructed ones.

For each object used, the spatial premise is
`HasStableNeighbourhoods H X.LocalSpectrum`: every open neighbourhood of a
local point contains a neighbourhood stable under an open subgroup. The local
instance `inducedStable` constructs
`HasStableNeighbourhoods G X.InducedSpectrum` using
`SpatialSheaves.hasStableNeighbourhoods_induced`. Ambient stable
neighbourhoods are not an additional independent input, and this module does
not assert that the local premise always holds.

The coefficient ring `R : Type u` is any commutative ring. Coefficients range
over all of `Langlands.SmoothRep.{u,u,u} R G`, with their original carriers and
all original linear intertwiners. There is no topology, finite-dimensionality
or admissibility premise on a coefficient module. Smoothness is the original
open-stabilizer property. Section modules belong to `ModuleCat.{u} R`; no
universe-lifting comparison is asserted.

For a morphism `f : X ⟶ Y`, its actual continuous equivariant map is

```text
f.inducedMap [a,x] = [a * f.label⁻¹, f.localSpectrumMap x].
```

The local spectrum map is the existing pullback of the bounded rational
restriction. The inverse label and the complete balanced quotient are retained.
Pullbacks and smooth direct images require no covering premise. Trace requires
`IsCoveringMap f.inducedMap` and finiteness of every literal fiber
`f.inducedMap ⁻¹' {y}`. These predicates concern this original map and are
not proved for arbitrary rational morphisms. Empty fibers are permitted and
contribute zero. No properness, compact-support, subgroup-normality or
separation assumption is added.

## Smooth image and full coefficient pullback

Write `L_X` for `coefficientFunctor R X` and `S_f` for `directImage R f`.
The functor `L_X` is exactly
`SpatialSheaves.smoothInducedCoefficientFunctor X R`. Its underlying ordinary
sheaf contains every locally constant section of the original coefficient
module on each ordinary open. The existing smoothness theorem bundles this
entire sheaf in the smooth category without replacing its sections.

`S_f` is `SmoothDirectImage.functor` on the actual `f.inducedMap` and its
proved full-group equivariance. It includes a smooth sheaf into ordinary
equivariant sheaves, takes the full ordinary direct image, and applies the
existing smooth coreflector on `Y`. Over an open `U`, its sections carry their
original inverse-open section together with local smoothness measured on `Y`.
This construction does not assume that the ordinary direct image of every
smooth sheaf is smooth.

`inclusion R f` embeds this functor into `SheafVariation.directImage` after
forgetting smoothness. `coefficientMap R f M` has direction

```text
L_Y(M) → S_f(L_X(M)).
```

It is the generic smooth coefficient pullback. The existing universal property
lifts the original full pullback from the already smooth source. The theorem
`coefficientMap_inclusion` identifies its composite with `inclusion` with
exactly `SheafVariation.coefficientMap f M.representation`.
`coefficientMap_apply` evaluates its underlying section by precomposition with
the original point map on `f⁻¹(U)`. `coefficientMap_mk_apply` evaluates the
same map at a quotient representative as

```text
(f* s)([a,x]) = s([a * f.label⁻¹, f.localSpectrumMap x]).
```

`coefficientNatTrans` has components `coefficientMap`, and
`coefficientMap_naturality` records its square for every original smooth
coefficient intertwiner.

`directImageIdIso R X` is oriented `𝟭 ≅ S_(𝟙 X)`. It combines the generic
smooth identity unit with equality transport through
`SheafVariation.inducedMap_id_eq`. The theorem `coefficientMap_id` identifies
the rational identity pullback with its forward component.

`directImageCompMap R f g` has direction

```text
S_f ⋙ S_g → S_(f ≫ g).
```

It is the actual generic lax `SmoothDirectImage.compMap`, followed by equality
transport through `SheafVariation.inducedMap_comp_eq`. No invertibility
premise or inverse of this lax map is used. The theorem `coefficientMap_comp`
proves

```text
b_(f ≫ g)(M) =
  b_g(M) ≫ S_g.map(b_f(M)) ≫ directImageCompMap(f,g).app(L_X(M)).
```

Here `b_f` denotes the constructed coefficient pullback.

## Trace, original fibers and all coefficients

Under the stated covering and finite-fiber premises,
`coefficientTrace R f hf M` has direction

```text
S_f(L_X(M)) → L_Y(M).
```

It is the generic smooth covering trace on the actual rational map. Forgetting
smoothness gives the exact equality `coefficientTrace_forget`: the resulting
full sheaf morphism is `inclusion.app(L_X(M))` followed by
`SheafVariation.coefficientTrace f hf M.representation`. The target remains
the complete, already smooth coefficient sheaf. Labelled restriction
compatibility is inherited from the actual inclusion and full trace.

For a section `s` of the smooth direct image over an arbitrary ordinary target
open `U`, `coefficientTrace_apply_sum` proves

```text
Tr_f(s)(y) = ∑ x : f.inducedMap⁻¹{y}, s.val(x).
```

The sum ranges over the entire literal original fiber. Each point is inserted
into the inverse open using its fiber equality and the membership of `y` in
`U`. The section `s.val` is the original locally constant section after
forgetting its smoothness proof. A `Fintype` is used only to display the finite
sum; the trace construction obtains one from the finiteness premise.

`coefficientTrace_pullback_apply` proves the pointwise degree formula

```text
Tr_f(f* s)(y) = Nat.card(f.inducedMap⁻¹{y}) • s(y).
```

The multiplier acts by natural-number scalar multiplication. It may vary
with `y`; there is no division, normalization or constant-degree hypothesis.
`coefficientTrace_pullback_mk_apply` evaluates this formula at the actual
inverse-label image `[a * f.label⁻¹, f.localSpectrumMap x]`.

`coefficientTraceNatTrans R f hf` is a natural transformation

```text
L_X ⋙ S_f → L_Y.
```

Its components are the constructed traces.
`coefficientTrace_naturality` proves the square for every original smooth
coefficient map `a : M ⟶ N`: direct image of the pointwise coefficient map
followed by trace at `N` equals trace at `M` followed by the original
pointwise map on `Y`. This uses finite-sum linearity in the generic trace;
the coefficient category and its morphisms are unchanged.

## Identity, composition and implemented proofs

For identity transport, `Hom.finite_inducedMap_id_fiber` supplies finite
fibers and `Hom.isCoveringMap_inducedMap_id` supplies covering.
`coefficientTrace_id` identifies the trace with
`(directImageIdIso R X).inv.app(L_X(M))`. The natural-transformation version
`coefficientTraceNatTrans_id` uses left whiskering of that same inverse
comparison. The identity pullback and trace therefore use opposite directions
of the actual smooth identity isomorphism.

For `f : X ⟶ Y` and `g : Y ⟶ Z`, `coefficientTrace_comp` proves

```text
directImageCompMap(f,g).app(L_X(M)) ≫ Tr_(f ≫ g)(M) =
  S_g.map(Tr_f(M)) ≫ Tr_g(M).
```

Covering and finite literal fibers are explicit for `f`, `g` and `f ≫ g`.
Composite finiteness is available from
`Hom.finite_inducedMap_comp_fiber`; composite covering remains an input.
`coefficientTraceNatTrans_comp` states the same equality on the whole
coefficient category. Its left side uses left whiskering of the actual lax
comparison, and its right side uses right whiskering of the trace for `f`
by `S_g`, followed by the trace for `g`.

The private helper `directImage_congr` identifies smooth direct-image functors
by substituting equality of continuous maps. The other congruence helpers
transport the generic pullback and trace laws by the same substitution and
proof irrelevance. The rational laws then apply these helpers to the existing
identity and composition equalities of `inducedMap`. In particular,
`trace_comp_congr` proves the transported generic lax law before its rational
specialization; no rational cast compatibility is assumed. Naturality is
inherited from the constructed generic natural transformations, and their
identity and composition equations follow componentwise. All intrinsic
equalities displayed above are proved.

## Remaining scope

This is a construction on ordinary-open degree-zero smooth coefficient
sheaves of actual rational spectra satisfying the explicit local
stable-neighbourhood and covering hypotheses. General rational covering and
stable-neighbourhood theorems, analytic or etale-site comparison, Godement
and higher derived traces, geometric compact-support comparisons, arithmetic
Hecke identification, Shimura towers and Harris compatibility remain
obligations of the broader task. This unit does not complete that task.
