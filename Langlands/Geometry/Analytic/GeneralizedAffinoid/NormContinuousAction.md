# Norm-continuous actions on actual positive-polyradius affinoid quotients

Authors: Worker 56 and Worker 36.

This derived construction extends Worker 36's published
[strict action category](../NormContinuousAction.md) to the actual
`PresentedAffinoidAlgebra K` quotients of arbitrary finite positive-polyradius
Tate algebras. It retains every equivariant bounded algebra map and constructs
a contravariant functor to continuous actions on the actual bounded
multiplicative spectra. The category and most categorical proofs adapt that
strict implementation; the spectrum continuity argument applies the generic
joint-evaluation theorem directly to these weighted quotients.

All declarations are in `Langlands.Analytic.PresentedAffinoidAlgebra`, with
the object, morphism, restriction and spectrum interfaces in the nested
namespace `NormContinuousAction`.

## Actual algebras and continuous orbits

The coefficient field `K` is an ultrametric normed field in universe `u`.
The group `G`, in independent universe `v`, initially has an arbitrary
topology. The imported `Definitions` module constructs an algebra from a
finite positive polyradius and a closed ideal in the corresponding weighted
Tate algebra. Its carrier is the actual ring quotient, with the quotient norm;
its category has all bounded `K`-algebra maps as arrows.

`normContinuousActionProperty K G` is the property on Mathlib's
`Action (PresentedAffinoidAlgebra K) G` requiring

```
for every a : X.V, the map g ↦ (X.ρ g)(a) is continuous.
```

Continuity is in the topology of the actual quotient norm.
`NormContinuousAction K G` is the full subcategory for this property.
`NormContinuousSpace K G` is its opposite, giving the geometric direction.
Neither these categories nor the spectrum constructions require coefficient
completeness. When `K` is complete the imported quotient constructions are
complete; over an incomplete field the present scope is the constructed
normed algebras and their spectra.

`ofAut` bundles a specified homomorphism `ρ : G →* Aut P` and continuous
forward element orbits. `actionAut` is the group-action lift provided by
Mathlib: the forward bounded map is `X.ρ g` and its bounded inverse is
`X.ρ (g⁻¹)`. `actionAut_ofAut` recovers the specified homomorphism.
`continuous_orbit` exposes the object property in these terms. Bounded
inverses come from the group action; no bounded inverse theorem is assumed.
`trivial` constructs an object over every presented quotient.

`homMap` extracts an arrow's actual bounded algebra map. Conversely,
`homMk` admits every bounded map satisfying
`X.ρ g ≫ f = f ≫ Y.ρ g` for all `g`.
`homMap_homMk` recovers that map, and `homMap_apply_action` is the
elementwise equivariance equation. `hom_ext` reduces arrow equality to
equality of retained bounded maps. The action category and full subcategory
supply identities and composition. `inclusion` into the action category is
full and faithful; `forget` to the category of actual quotient algebras is
faithful.

## Continuous group restriction

For a group `H` in independent universe `w` and a continuous group
homomorphism `f : H →ₜ* G`, `restrict f` lifts Mathlib's `Action.res`.
Each new orbit is the original orbit composed with `f`, which proves its
continuity. The actual algebra and the bounded map of every arrow are
retained. `restrict_obj_algebra`, `restrict_obj_apply` and
`homMap_restrict_map` expose these equalities. Restriction is faithful
because its morphism map retains the bounded map.

## Inverse pullback on actual spectra

For any presented algebra `A`, `spectrumMulAction` constructs an action
of the abstract group `Aut A` on `BanachSpectrum A` by

```
(g • x)(a) = x(g.inv(a)).
```

The inverse makes contravariant seminorm pullback a left action.
`smul_spectrum_apply` records this formula. The identity and product laws
hold by evaluation on every algebra element. Each individual action map
is continuous, by the existing bounded pullback map;
`spectrumContinuousConstSMul` records this fact. These instances assign no
topology to `Aut A` and assert no joint continuity for that group.

For `X : NormContinuousAction K G`, `spectrumAction X` bundles the same
inverse-pullback maps as an `Action TopCat G`. Its underlying space is
exactly `BanachSpectrum X.obj.V`. `spectrumAction_apply` gives its
elementwise formula. This construction needs no continuity of group
operations.

Under `IsTopologicalGroup G`, `spectrum X` bundles this action as a
`ContAction TopCat G`, with joint continuity proved rather than supplied
as input. For each `a`, the orbit of `a` under the inverse automorphism
is the forward orbit composed with group inversion, hence is continuous.
The theorem `BanachSpectrum.continuous_comap_of_continuous_apply`
then gives continuity of `(g,x) ↦ x ∘ (X.actionAut g).inv`.
That theorem uses the evaluation topology and the proved estimate
`|x(a) - x(b)| ≤ ‖a - b‖` to obtain joint evaluation continuity.
Thus no common operator norm bound on the whole group is required.

For every equivariant bounded map `f : X ⟶ Y`,
`spectrumMap_equivariant` proves that seminorm pullback intertwines
the two spectrum actions. Its proof evaluates at `a` and uses the
algebra-map equivariance equation at `g⁻¹`.
Consequently `spectrumFunctor` is a functor

```
NormContinuousSpace K G ⥤ ContAction TopCat G.
```

On arrows it is the actual continuous pullback along `homMap f.unop`.
Identity and composition laws follow by evaluating the resulting
seminorms. `spectrumFunctor_map_apply` records that arrow formula.

Mathlib's continuous-action category retains a specified forgetful
functor to `TopCat`. This module installs the identity forgetful functor
from [TopCatSelfForget](../../../CategoryTheory/TopCatSelfForget.md)
locally. Downstream code can spell the same target using
`attribute [local instance] Langlands.Analytic.NormContinuousAffinoidAction.topCatSelfForget`.

Zero presentation arity, trivial valuations, nonreduced and zero quotients,
and empty spectra are permitted. No local compactness or separation
hypothesis on `G` is added. This module does not identify the norm-orbit
condition with the topology on analytic automorphisms, construct general
analytic atlases, or define étale or equivariant sites.

## Original sources and derived provenance

Berkovich, *Non-archimedean analytic spaces* (Trieste lectures, 2009),
printed/PDF p. 4, Example 1.2.2(v), Definitions 1.2.3 and 1.2.5 and
Exercise 1.2.4, supplies the positive-radius series, bounded multiplicative
spectrum and evaluation-topology context. Definition 2.1.2, p. 7, gives
the general affinoid quotient presentation; Definition 2.1.11, p. 8,
gives the dual category with bounded algebra maps. The source works over
complete fields. The incomplete-field scope here is only the constructed
normed quotient and spectrum infrastructure.
Registered original: `berkovich-2009-trieste-analytic-spaces`,
PDF SHA256
`8cfe4f6f35d5e717ac67c5c8f5ef9ff9185f460bbe5f9a10aeacd84cddeeb2ca`.

Berkovich's unfinished *Étale equivariant sheaves on p-adic analytic spaces*
(1995–1996), section 1.1, printed/PDF pp. 1–3, defines analytic
automorphism topology, continuous analytic actions, equivariant
morphisms and morphisms that change the group through a continuous
homomorphism. These motivate this fixed-field local construction.
The present norm-orbit category is not identified with that manuscript's
full `G-An`; its section 1.2 sites remain further obligations.
Registered original:
`provided-7bb3903652336bd799aad8853b8efd7ff3bcc0c7652745417f4745a14ac08e90`,
folder SHA256
`e046cadfb9dcec4b0cf6624f80d6316bf532416153b82023f5100bd1ab0726cd`,
member `Berkovich--Etale equivariant sheaves on p-adic analytic spaces (unfinished manuscript)--1996.pdf`,
member SHA256
`91567a75866a27cbe6690b6f075693df5afaa02524223d94d52ea37d77bb6637`.
These original passages were read directly.

The precise category, restriction and spectrum functor are internal
derived constructions, not numbered results attributed to these sources.
They reuse the published actual weighted quotient category, bounded
spectrum pullback, joint evaluation and parametric-pullback continuity,
and Mathlib's action, full-subcategory and continuous-action interfaces.
The constructions and proofs above describe the implemented Lean route.
