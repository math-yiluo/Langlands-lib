# Functorial induction of actual affinoid actions

Author: Worker 56.

This module constructs induction on equivariant bounded maps between actual
positive-polyradius affinoid inputs. It packages the induced families as a
functor, constructs the maps on their actual balanced spectrum quotients,
and proves a natural equivariant comparison with spectrum realization.
For an open subgroup over a complete coefficient field, it constructs
bounded maps of the quotient atlases, including pullbacks on every
admissible chart pair, and a functor to chosen atlas presentations.

All declarations lie in
`Langlands.Analytic.PresentedAffinoidAlgebra.InducedAction`.
The module reuses [InducedAction](InducedAction.md) for its object
construction and retains its algebras, actions, charts and topologies.

## Input categories and assumptions

Let `K : Type u` be a normed field with ultrametric distance, `G : Type v`
a group with a topology, and `H : Subgroup G` with its inherited topology.
An object `X : NormContinuousSpace K H` is an object of the opposite of
the published category of norm-continuous subgroup actions on presented
positive-polyradius affinoid quotient algebras. Write `A_X = X.unop.obj.V`.
For a geometric arrow `f : X ⟶ Y`, its retained bounded algebra map is

`f* = NormContinuousAction.homMap f.unop : A_Y → A_X`.

Every equivariant bounded algebra map is allowed; the input category is
full. In particular, no assumption that spectrum points detect algebra
maps is made. Nilpotents and the entire original quotient algebra remain
present.

The family functor requires neither openness of `H` nor continuity of the
group operations. The balanced quotient constructions require
`[IsTopologicalGroup G]`. The spectrum comparison also requires
`hH : IsOpen (H : Set G)`. The atlas constructions additionally require
`[CompleteSpace K]`. No finite-index, nonempty-spectrum, reducedness,
radius-one, local compactness or separation hypothesis is added.
The family index has universe `v`, and the realized spectra and quotient
spaces have universe `max u v`.

## Equivariant bounded family functor

`familyMap H f` maps the induced family of `X` to that of `Y`. It keeps
each coset `c : G ⧸ H` fixed and uses precisely `f*` as the bounded
pullback on that component. `familyMap_pullback` records this equality.

`familyMap_comm` proves that this family map commutes with every
full-group action map:

`actionMap X g ≫ familyMap f = familyMap f ≫ actionMap Y g`.

The index functions agree. On the original algebras, the proof uses
equivariance of `f*` at the inverse of the representative correction
`κ(g,c)` constructed in `InducedAction`. Thus it proves equality of
bounded maps directly. It does not infer that equality from seminorms.

`familyMap_id` and `familyMap_comp` prove the identity and composition
laws by extensionality on the retained bounded maps. `functor` packages
the resulting construction as

```
NormContinuousSpace K H ⥤ Action (AffinoidFamily K) G.
```

For open `H`, `spectrumFunctor` applies the actual family-spectrum
functor to this categorical action and uses the already proved joint
continuity of `InducedAction.continuousSpectrum` on every object.
Its target is `ContAction TopCat G`, with spaces in universe `max u v`.
The module installs the published identity forgetful functor on `TopCat`
locally, as required by Mathlib's continuous-action category.

## Functor on actual balanced quotients

`balancedAction H X` bundles the existing full-group action on
`Spectrum H X.unop`, the actual quotient
`G ×_H LocalSpectrum H X.unop`, as a continuous categorical action.
The group laws are those of the quotient action; joint continuity is
the published quotient continuity theorem. This construction does not
replace the quotient topology and does not require openness of `H`.

`localSpectrumMap H f` is the continuous seminorm pullback along `f*`
on the original subgroup spectra. `localSpectrumMap_equivariant`
uses the equivariance theorem from `NormContinuousAction`.
The private lemma `localSpectrumMap_unit` composes this with the
subgroup-equivariant inclusion into the balanced quotient.

`balancedMap H f` uses the published continuous quotient extension of
that map. Its representative formula is

`balancedMap f [g,x] = [g,localSpectrumMap f x]`.

This is `balancedMap_mk`. `balancedMap_equivariant` proves equivariance
for every `g : G` by the quotient extension's equivariance theorem.
`balancedFunctor` packages these maps in

```
NormContinuousSpace K H ⥤ ContAction TopCat G.
```

Its identity and composition proofs use quotient induction and the
representative formula. `balancedMap_id` and `balancedMap_comp` expose
the resulting equalities of continuous maps, in particular

`balancedMap (f ≫ k) = (balancedMap k).comp (balancedMap f)`.

For open `H`, `spectrumHomeomorph_naturality` proves that the actual
coset-family-to-quotient homeomorphism commutes with every induced map.
On a component `(c,x)`, both sides are
`[c.out,localSpectrumMap f x]`. `spectrumComparison` packages these
homeomorphisms as a natural isomorphism

`spectrumFunctor H hH ≅ balancedFunctor H`.

Its components are equivariant by the action realization theorem of
`InducedAction`; its naturality is the preceding formula. All source
and target topologies are the original spectrum and quotient topologies.

## Bounded quotient-atlas maps

Under coefficient completeness and openness of `H`,
`atlasPresentation H hH X` bundles the actual quotient space and the
atlas already constructed in `InducedAction`. Its chart indices are
cosets carrying a nonempty original spectrum, and every chart algebra
is the original `A_X`.

`mapChart H hH f c` constructs a target chart in the same coset as `c`.
Its nonemptiness follows by pulling back a source seminorm along `f*`.
`mapChart_id` and `mapChart_comp` prove its categorical laws.
`mapChart_subset` proves that the quotient map sends the source chart
into this target chart.

`mapChart_eq` proves that every target chart containing that image is
the constructed target. It transports the containment through the actual
spectrum homeomorphism and uses the corresponding uniqueness theorem
for nonempty disjoint family charts. Thus this conclusion also holds
when the ambient induced spectrum is empty: in that case there is no
source chart to which the quantified assertion must be applied.

For every pair `(c,d)` satisfying the required image containment,
`mapPullback H hH f c d h` is precisely `f*`. Its source and target are
the original component algebras. `mapPullback_chart` identifies its
spectral realization with `balancedMap f` by first identifying `d`
with `mapChart f c` and then using the representative formula.

`mapPullback_naturality` proves commutation with both source and target
atlas restrictions as an equality of bounded algebra maps. Containment
of two nonempty charts in each of these disjoint atlases identifies
their indices. The atlas restriction identities then reduce the
equation to the retained bounded map. `strongMap` packages the actual
continuous map, target existence, and all these admissible-pair
pullbacks as `AffinoidAtlasPresentation.StrongHom`.

`atlasMap` chooses the unique admissible same-coset target. Monotonicity
of this choice follows from equality of source indices whenever one
chart contains another. Its bounded restriction compatibility is the
special case of `mapPullback_naturality` at the chosen targets.
`atlasMap_id` and `atlasMap_comp` prove equality of base maps, chosen
indices and bounded pullbacks. `atlasFunctor` therefore has type

```
NormContinuousSpace K H ⥤
  AffinoidAtlasPresentation.{u, max u v, v} K.
```

`mapPullback_id` records the bounded identity at a chart.
`mapPullback_comp` proves the contravariant composition equation for
every compatible admissible triple `(c,d,e)`:

`mapPullback (f ≫ k) c e = (mapPullback f c d).comp (mapPullback k d e)`.

These equations follow from the original bounded identity and
composition in the input category. They preserve algebraic information
that the spectrum need not detect.

## Provenance and scope

The original motivation is Berkovich's unfinished *Etale equivariant
sheaves on p-adic analytic spaces* (1995–1996), Construction 1.1.2,
printed/PDF page 2. It constructs induction for an open subgroup by
copies of the subgroup space indexed by `G/H`, with action determined
by `g*g_i = g_j*h`, and states the analytic extension universal property.
The original page was read directly for this contribution.

Registered source:
`provided-7bb3903652336bd799aad8853b8efd7ff3bcc0c7652745417f4745a14ac08e90`;
folder SHA256
`e046cadfb9dcec4b0cf6624f80d6316bf532416153b82023f5100bd1ab0726cd`;
member
`Berkovich--Etale equivariant sheaves on p-adic analytic spaces (unfinished manuscript)--1996.pdf`;
member SHA256
`91567a75866a27cbe6690b6f075693df5afaa02524223d94d52ea37d77bb6637`.

The functors and atlas maps here are internal derived constructions for
the actual affinoid-input case of that coset-copy construction.
Their proofs use equivariance of the original bounded map, the existing
balanced quotient extension and homeomorphism, and uniqueness of
nonempty disjoint chart targets. The constructions reuse
`GeneralizedAffinoid.NormContinuousAction`,
`GeneralizedAffinoid.InducedAction`, `DisjointAffinoidMorphisms`,
`DisjointAffinoidTransport`, `ChosenAtlasMorphisms`, `StrongAtlasMaps`
and `Topology.GroupAction.InducedSpace` by Lean import and declaration
name. No output atlas or universal extension in an analytic category is
assumed.

This module constructs functorial bounded maps of the induced atlases
and equivariance of the family and spectrum maps. It does not yet
package a full-group action in the chosen-atlas morphism category or
identify norm-orbit continuity with Berkovich's analytic automorphism
topology. Induction for arbitrary overlapping atlases, the analytic
adjunction, etale and quasi-etale sites, and the Harris specialization
remain separate obligations.
