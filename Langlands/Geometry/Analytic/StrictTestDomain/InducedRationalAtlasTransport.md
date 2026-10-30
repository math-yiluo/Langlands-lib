# Bounded transport on the actual induced affinoid atlases

Author: Worker 36.

This module constructs bounded pullbacks on the actual positive-polyradius
quotient algebras of the published induced affinoid atlases. The pullbacks
retain the subgroup correction associated with chosen coset representatives.
They form a functor to `AffinoidFamily K`, realize the existing transport on
the actual balanced quotient, and give compatible maps for every admissible
source and target atlas chart.

## Sources and provenance

Berkovich, *Étale cohomology for non-Archimedean analytic spaces* (1993),
section 1.2, Definition 1.2.7, printed page 18 / PDF page 15, specifies a
continuous map carrying each source chart into some target chart and a
compatible affinoid morphism for every pair with the required containment.
The composition discussion on the same page uses extended atlases and
gluing in general. Here the disjoint component atlases permit an explicit
composition of bounded homomorphisms. Registered source:
`berkovich-1993-etale-cohomology`, PDF SHA256
`06b42aca1c8f237e607d2cf1f15a41fdc9718324a4dc9fd5bce66574254bb91c`.
The rendered original confirms printed page 18; its extracted text
misreads the page header.

Berkovich, *Non-archimedean analytic spaces* (Trieste lectures, 2009),
Definition 2.1.11, printed/PDF page 8, defines affinoid spaces as the
category dual to affinoid algebras with bounded homomorphisms. This fixes
the direction of the pullbacks. Registered source:
`berkovich-2009-trieste-analytic-spaces`, PDF SHA256
`8cfe4f6f35d5e717ac67c5c8f5ef9ff9185f460bbe5f9a10aeacd84cddeeb2ca`.

Berkovich's unfinished *Etale equivariant sheaves on p-adic analytic
spaces*, retained Equish_1996 manuscript (1995–1996), Construction 1.1.2,
printed/PDF page 2, constructs induction from an open subgroup as a
disjoint union indexed by left cosets. Changes between chosen
representatives introduce subgroup operators. Registered folder source:
`provided-7bb3903652336bd799aad8853b8efd7ff3bcc0c7652745417f4745a14ac08e90`,
folder SHA256
`e046cadfb9dcec4b0cf6624f80d6316bf532416153b82023f5100bd1ab0726cd`.
The member *Berkovich--Etale equivariant sheaves on p-adic analytic spaces
(unfinished manuscript)--1996.pdf* has SHA256
`91567a75866a27cbe6690b6f075693df5afaa02524223d94d52ea37d77bb6637`.

All three original passages were read. No source-specific errata note was
present in the workspace, current Library or shared project notes.
The functor and formulas below are derived constructions from the published
actual rational pullbacks, strict/generalized quotient comparison, disjoint
family category and induced affinoid atlas. They are not separately numbered
results in the sources.

## Hypotheses and actual quotient objects

Work in
`Langlands.Analytic.StrictTestDomain.RationalAutomorphism.RationalSpectralAction.OpenSubgroupTransport`.
The coefficient field `K : Type u` is complete, normed and ultrametric.
The ambient `P` is a presented strict affinoid algebra, `G : Type v` is
a topological group, and `ρ : RationalSpectralAction G P`.
The universes `u` and `v` are independent.

For an object `X : ρ.OpenSubgroupTransport`, write `H_X` for its open
subgroup, `A_X` for `X.domain.obj.algebra`, and `B_X` for
`X.inducedChartAlgebra`. The algebra `A_X` is the constructed rational
closed-ideal Tate quotient. The algebra `B_X` is its actual radius-one
positive-polyradius quotient presentation. The imported bounded
equivalence is

`E_X = PresentedAffinoidAlgebra.strictEquiv K A_X : B_X ≃ A_X`.

`inducedAffinoidObject X` has index type `G/H_X` and the constant
algebra family `B_X`. Its space is the actual topological sum of the
spectra of `B_X`. The published `X.inducedAffinoidHomeomorph` identifies
that sum with the actual balanced quotient `X.InducedSpectrum`.
`X.inducedAffinoidAtlas` uses precisely its nonempty component spectra
as charts, with the published bounded identity restrictions.

## Bounded pullbacks and functor laws

Let `f : X ⟶ Y`. Its component function is the existing `f.cosetMap`.
The imported `f.cosetChartPullback c : A_Y → A_X` is the bounded
rational chart pullback at `c.out` and `(f.cosetMap c).out`. It includes
the target subgroup operator comparing these representatives. The new
`cosetChartPullback_id` and `cosetChartPullback_comp` specialize the
published compatible-chart algebra laws to the chosen representatives.
The latter reads

`(f ≫ g).cosetChartPullback c =
  (f.cosetChartPullback c).comp (g.cosetChartPullback (f.cosetMap c))`.

`affinoidChartPullback f c : B_Y → B_X` is the actual bounded composite

`E_X.symm ∘ f.cosetChartPullback c ∘ E_Y`.

`affinoidChartPullback_id` cancels the inverse algebra equivalence after
using the rational identity law. `affinoidChartPullback_comp` uses the
rational composition law and cancels `E_Y ∘ E_Y.symm` on each algebra
element. These are equalities of bounded algebra homomorphisms; they are
not deduced from equality on spectrum points.

`affinoidFamilyMap f` has index map `f.cosetMap` and component pullback
`f.affinoidChartPullback`. The identity and composition laws follow from
the corresponding index and algebra laws using `AffinoidFamily.Hom.ext`.
`inducedAffinoidTransportFunctor` packages these objects and maps into

`ρ.OpenSubgroupTransport ⥤ AffinoidFamily.{u, v} K`.

## Realization on the balanced quotient

`affinoidChartPullback_spectrum` compares the spectrum comap in the two
quotient presentations. For `x : BanachSpectrum B_X` its equation is

```text
Y.localAffinoidSpectrumHomeomorph.symm
    (comap (f.affinoidChartPullback c) x)
  = f.cosetChartSpectrumMap c
      (X.localAffinoidSpectrumHomeomorph.symm x).
```

The proof evaluates the two seminorms on every algebra element and
cancels the actual algebra equivalence and its inverse.
`affinoidFamilyMap_realization` then states, for every point `p` of
the actual disjoint sum,

```text
f.inducedMap (X.inducedAffinoidHomeomorph p)
  = Y.inducedAffinoidHomeomorph
      (f.affinoidFamilyMap.spectrumMap p).
```

Its proof decomposes `p` into its component and spectrum point, uses the
published compatible-chart realization on the balanced quotient, and
uses the preceding spectrum comparison. Thus the functor's continuous
spectrum maps realize the existing induced transport through the
constructed homeomorphisms.

## Every admissible atlas chart pair

`atlasTarget f c` uses the published disjoint-family `chartTarget`.
The latter obtains a point of the nonempty source chart and comaps its
seminorm to prove that the target spectrum is nonempty. Accordingly this
constructor imposes no additional nonemptiness assumption.
`image_atlasChart_subset` proves that `f.inducedMap` maps the range of
chart `c` into that of `f.atlasTarget c`, using the realization above.

Suppose `d` is any target chart and

`h : f.inducedMap '' range (X.inducedAffinoidAtlas.chart c)
       ⊆ range (Y.inducedAffinoidAtlas.chart d)`.

`disjointChart_containment` pulls this containment back through the
actual chart homeomorphisms, using injectivity of the target
homeomorphism and the realization equation. The published
disjoint-family `chartTarget_eq` then proves `atlasTarget_eq f c d h`.

`atlasPullback f c d h` is `f.affinoidChartPullback c.val`, of type

`BoundedAlgHom K (Y.inducedAffinoidAtlas.algebra d)
  (X.inducedAffinoidAtlas.algebra c)`.

The algebra families are constant, so no transport of its algebra type
is necessary. The containment proof is used to identify the target
chart in `atlasPullback_chart`, which proves

```text
chart_Y d (comap (f.atlasPullback c d h) x)
  = f.inducedMap (chart_X c x).
```

`atlasPullback_naturality` proves compatibility with restrictions in both
atlases. For contained charts `c ⊆ c'` and `d ⊆ d'`, with the two
corresponding admissibility proofs, its equation is

```text
restriction_X(c,c') ∘ atlasPullback(f,c',d')
  = atlasPullback(f,c,d) ∘ restriction_Y(d,d').
```

The proof rewrites both restrictions as bounded identities and uses
nonempty-component containment to identify `c = c'`; the remaining
algebra maps agree definitionally.

`atlasPullback_id` gives the bounded identity for an identity transport
arrow in the same chart. For `f : X ⟶ Y` and `g : Y ⟶ Z`, and every
triple `c,d,e` with the three required containments,
`atlasPullback_comp` proves

`atlasPullback(f ≫ g,c,e) =
  atlasPullback(f,c,d) ∘ atlasPullback(g,d,e)`.

It identifies `d.val = f.cosetMap c.val` using `atlasTarget_eq` and
applies the already proved algebra composition law.

## Scope

The construction permits empty local spectra and infinitely many cosets.
It supplies actual bounded maps for every admissible chart pair of these
constructed atlases. It does not introduce a general strong-morphism
structure or the localization of that category. The full-group action
on these chosen atlas algebras, general overlapping atlases and gluing,
structure sheaves, etale and equivariant sites, the full analytic
induction universal property and Harris's tower specialization remain
separate obligations.

The input `RationalSpectralAction` retains the restricted rational
spectral topology specified in `SpectralAction.lean`. This module makes
no comparison with the full analytic automorphism topology of the
unfinished manuscript.
