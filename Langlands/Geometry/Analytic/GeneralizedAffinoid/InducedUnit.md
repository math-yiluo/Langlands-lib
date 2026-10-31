# Bounded identity-coset unit for actual affinoid induction

Author: Worker 56.

This module constructs the unit from a genuine affinoid subgroup action to its
induced coset family, then realizes it as a natural subgroup-equivariant bounded
atlas map on the actual balanced quotient. Its continuous map sends a point
`x` to `[1,x]`. All equivariance and naturality equations compare complete
morphisms, including the original bounded algebra maps.

The Lean namespace is
`Langlands.Analytic.PresentedAffinoidAlgebra.InducedAction`.

## Inputs and geometric direction

Let `K : Type u` be a normed ultrametric field, `G : Type v` a group, and `H`
a subgroup. The identity-coset facts require no topology. The family
constructions additionally use a topology on `G` and an object
`X : NormContinuousSpace K H`. This is the geometric opposite of the full
category of actions on actual positive-polyradius affinoid quotient algebras
whose forward algebra element orbits are norm-continuous. Write `A_X` for
`X.unop.obj.V` and `α_X : H →* Aut A_X` for `X.unop.actionAut`.

A geometric arrow `f : X ⟶ Y` retains an equivariant bounded algebra map
`f* : A_Y → A_X`. The geometric `h`-action on the bounded multiplicative
spectrum is pullback by `α_X(h).inv`. Neither reducedness nor a radius-one
presentation is required. No equality of bounded algebra maps is deduced from
their action on spectrum points.

The realization statements require a topological group `G` and an open
subgroup `H`. The atlas constructions additionally require completeness of
`K`. Their space universe is `max u v` and their index universe is `v`.

## The unnormalized identity coset

`identityCoset H` is the left coset of `1`. The quotient's chosen representative
need not be `1`. `identityRepresentative H` constructs an element `r : H`
whose underlying element is this representative: membership in `H` follows
from the quotient equality with the identity coset.

`identityCoset_smul` proves that every `h : H` fixes this coset. Consequently,
`correction_identityCoset` identifies the existing correction element there as

```text
correction(H,h,identityCoset) = r⁻¹ h r.
```

This equality is proved in the subgroup by comparing the underlying group
elements and simplifying the actual correction formula. No normalized choice
of representatives is assumed.

## The original one-component action

`localFamily H X` is an actual `PUnit.{v+1}`-indexed affinoid family whose
algebra is `A_X`. It retains this algebra even if its spectrum is empty.
`localActionMap H X h` fixes the component index and has bounded pullback
`α_X(h).inv`. Its identity and multiplication laws are proved as equations of
entire family maps, using bounded inverses and the algebra action laws. The
multiplication equation is

```text
localActionMap(h*k) = localActionMap(k) ≫ localActionMap(h).
```

This is the multiplication convention for categorical endomorphisms and gives
`localAction H X : Action (AffinoidFamily K) H`.

`localFamilyMap H f` fixes the component index and retains precisely `f*` as
its pullback. Its complete equivariance equation follows from equivariance of
`f*` evaluated at `h⁻¹`. These objects and maps form `localFunctor H`. Its
identity and composition laws compare component indices and bounded algebra
maps directly.

## The bounded family unit

`unitFamilyMap H X` selects `identityCoset H`. Its bounded pullback is the
**forward** operator `α_X(r).hom`. The formula is necessary because the chosen
representative `r` need not be the identity.

`unitFamilyMap_equivariant` proves

```text
localActionMap(h) ≫ unitFamilyMap = unitFamilyMap ≫ actionMap(h).
```

The index equation is the fixed identity coset. For the algebra equation,
conjugation of the correction gives `h⁻¹ r = r correction(h,identityCoset)⁻¹`.
Applying the original algebra action to this equality proves equality of the
bounded pullback composites on every algebra element. In particular, this
argument preserves any nilpotent information.

`unitFamilyMap_naturality` compares the two composites for every original
geometric arrow `f`. Its algebra equation is exactly
`f* α_Y(r) = α_X(r) f*`. `familyUnit` packages these proved equations as a
natural transformation from `localFunctor H` to `functor H` followed by
restriction of the full-group action along `H.subtype`.

`unitFamilyMap_spectrumMap` computes its actual spectral map:

```text
x ↦ (identityCoset, r⁻¹ • x).
```

The proof identifies the inverse geometric `r`-action with pullback by the
forward operator, using the algebra action's inverse law. Applying the
existing coset-family-to-balanced-quotient homeomorphism therefore gives
`[r,r⁻¹ • x] = [1,x]`. The balanced relation proves this equality in
`unitFamilyMap_realization`. It identifies precisely the existing
`TopologicalInduction.unit H`, independently of the representative choice.

## The bounded atlas unit

`localAtlasFunctor H` realizes the original one-component family action with
the existing disjoint-family atlas functor. Such atlases retain only components
with nonempty spectrum. Thus the source and induced target have no charts when
the original spectrum is empty; no nonemptiness assumption or choice of a
chart in an empty target is introduced.

`unitAtlasMap H hH X` is the composite of the atlas realization of
`unitFamilyMap H X` with the existing bounded `atlasComparisonHom` from the
family spectrum to the actual balanced quotient. Both maps, their charts and
their bounded pullbacks are already constructed from the original algebras.

`unitAtlasMap_equivariant` and `unitAtlasMap_naturality` follow by the family
atlas functor's composition law, the corresponding complete family equations,
and the complete equivariance and naturality of `atlasComparisonHom`.
Associativity gives the required squares. These are equations of complete
chosen atlas morphisms, rather than equations only of their continuous maps.

`equivariantAtlasUnit` is the resulting natural transformation

```text
localAtlasFunctor H ⟶
  equivariantAtlasFunctor H hH ⋙ Action.res _ H.subtype.
```

The projection lemmas make its data explicit. `unitAtlasMap_indexMap` states
that every source chart maps to the identity coset.
`unitAtlasMap_pullback` states that its bounded pullback is exactly
`α_X(r).hom`, since the comparison pullback is the algebra identity.
`unitAtlasMap_baseMap_apply` states that its continuous map is exactly
`x ↦ [1,x]` on the one-component spectrum.

## Original source and derived content

The motivating original is Vladimir G. Berkovich, *Etale equivariant sheaves
on p-adic analytic spaces*, unfinished 1995–1996 manuscript,
Construction 1.1.2, printed/PDF page 2. The registered source identifier is
`provided-7bb3903652336bd799aad8853b8efd7ff3bcc0c7652745417f4745a14ac08e90`;
the registered publication-folder SHA256 is
`e046cadfb9dcec4b0cf6624f80d6316bf532416153b82023f5100bd1ab0726cd`.
The exact member is
`Berkovich--Etale equivariant sheaves on p-adic analytic spaces (unfinished manuscript)--1996.pdf`,
SHA256
`91567a75866a27cbe6690b6f075693df5afaa02524223d94d52ea37d77bb6637`.

The original chooses a representative `1` for the identity coset and includes
the original space as that copy. This Lean construction internally derives
the same normalized inclusion from the quotient's arbitrary chosen
representative. The conjugation formula, bounded forward correction, complete
family and atlas equations, and natural-transformation packaging are internal
implementation results. They are not quoted as separate theorems from the
manuscript.

This contribution supplies the bounded atlas unit for genuine affinoid input
actions. It does not identify norm-orbit continuity with Berkovich's topology
on analytic automorphisms, extend induction to arbitrary overlapping atlases,
or prove the analytic extension universal property or an analytic adjunction.
The analytic sites and the Harris specialization remain separate construction
obligations.
