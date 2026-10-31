# Continuous families through nested actual rational charts

Author: Worker 56.

This module constructs equivalences of compatible continuous families through
an actual inclusion of rational charts. It handles both the forward
finite-cover functor and its constructed inverse on every outer cover,
compares restriction and quotient gluing, and identifies the two family
round trips with pullback through the cover equivalence's unit and counit.

## Inputs and actual geometry

The field `K` is a complete ultrametric normed field. The base
`A : PresentedAffinoidAlgebra K` is an actual quotient of a finite
positive-polyradius Tate algebra by a closed ideal, with its quotient norm
and chosen presentation. The rational charts `d` and `e` over `A` retain
arbitrary positive radii and an explicit unit-generation hypothesis.
A chart arrow `f : d ⟶ e` has an actual bounded restriction
`e.algebra → d.algebra` over `A`. Its spectrum map goes from the inner
chart `d` to the outer chart `e` and is a proved closed embedding.

A full domain `U : Domain K d.algebra` carries its representing algebra,
bounded structural map, closed locus, exact spectrum image and unique
factorization against every presented affinoid test. Write `N U` for
`nestedDomain f U`. This is the already constructed full domain over
`e.algebra`, retaining `U.algebra` and composing its structural map with
the actual chart restriction. Its locus is the image of `U.locus` under
`f.spectrumMap`.

Write

```
H_V = nestedDomainLocusHomeomorph f V :
        V.locus ≃ₜ (nestedDomain f V).locus.
F   = nestedFiniteCoverFunctor f U.
G   = nestedFiniteCoverInverse f U.
```

The forward map of `H_V` is the restriction of `f.spectrumMap`.
`nestedDomainLocusHomeomorph_symm_spectrumMap` records that its inverse
lifts the supplied actual outer spectrum point:
`f.spectrumMap (H_V.symm x) = x` on underlying points.
`nestedDomainLocusHomeomorph_symm_naturality` proves that these inverse
homeomorphisms commute with every retained domain inclusion. Its proof
applies injectivity of the target homeomorphism, then uses its inverse
laws and the existing forward naturality equation.

A finite cover `c` contains actual full component domains `c.obj i`,
their actual inclusions into `U`, and a proof of coverage. The forward
cover `F.obj c` retains its size, component algebras and bounded
restrictions, and replaces each component by `N (c.obj i)`.
The space `Y : Type v` is any topological space, in an independent
universe. No separation assumption on `Y` is used.

## Forward families and their inverse

For a family `g_i : C((c.obj i).locus, Y)`,
`nestedCoverFamily f c` is the componentwise map

```
(T_c g)_i = g_i.comp H_(c.obj i).symm.
```

`nestedCoverFamilyInverse f c` uses the forward homeomorphism:
`(R_c g)_i = g_i.comp H_(c.obj i)`.
These definitions act on all continuous families, before overlap
compatibility is imposed.

The existing `c.Compatible g` means that values agree whenever two
component-locus points have equal underlying points in the base spectrum.
For `compatible_nestedCoverFamily`, equality of the transported points
implies equality of their inverse lifts by injectivity of
`f.spectrumMap`; the original compatibility then applies.
For `compatible_nestedCoverFamilyInverse`, apply `f.spectrumMap` to the
original equality and use the supplied transported compatibility.
The two family inverse laws follow componentwise from the inverse laws
of the actual homeomorphisms, using continuous-map extensionality.

`nestedCoverFamilyEquiv f c` packages these constructions as

```
CompatibleFamily c Y ≃ CompatibleFamily (F.obj c) Y.
```

The subtype inverse laws use the proved equalities of all component maps.
No family equivalence or inverse map is supplied as an input.

## Global restriction, spectrum assembly and gluing

`nestedCoverFamily_restrict` states that transport of the restriction of
`h : C(U.locus, Y)` equals restriction of `h.comp H_U.symm` to the
forward cover. The proof applies the inverse locus naturality equation
to each actual component inclusion.
`nestedCoverFamilyEquiv_gluingEquiv` is the corresponding equality for
the existing `gluingEquiv`. The forward map of that equivalence is
restriction; its inverse is the actual quotient-lift glued map.

The imported `DomainGluing.glue` first assembles the continuous maps on
the finite disjoint union of the actual component Banach spectra. The
overlap condition makes this map constant on fibers of the actual cover
total map, and the proved quotient-map property supplies its continuous
lift to the target locus.
`glue_nestedCoverFamily` identifies this constructed glued map:

```
glue_(F.obj c) (T_c g) = (glue_c g).comp H_U.symm.
```

The proof uses uniqueness of that quotient glue and checks its
restrictions with `nestedCoverFamily_restrict` and `restrict_glue`.

`nestedCoverFamily_spectrumFamilyMap` proves that assembly on the
disjoint union of actual spectra is unchanged. Both sides have the
same source because every representing component algebra is retained.
The existing `nestedDomain_spectrumToLocus` equation, followed by the
inverse law of `H_(c.obj i)`, identifies the two evaluations.

## Refinements and the forward presheaf comparison

A refinement `r : Refinement b c` has a chosen index function and
actual bounded component restrictions. Its pullback acts from families
on `c` to families on `b`.
`nestedCoverFamily_pullbackFamily` proves, even without overlap
agreement,

```
T_b (r.pullbackFamily g)
  = (nestedCoverRefinement f r).pullbackFamily (T_c g).
```

The component proof uses inverse locus naturality for `r.map i`.
`nestedCoverFamilyEquiv_pullback` gives this equation for compatible
families. `pullbackEquiv_trans_nestedCoverFamilyEquiv` states it as an
equality of equivalences, with the same variance.
`nestedCoverFamilyEquiv_pullbackEquiv_symm` also compares the inverses
of refinement pullback. Those imported inverses glue the finer family
and restrict the glued map to the coarser cover. The proof applies
injectivity of the transported pullback equivalence, uses the forward
square, and cancels both inverse laws.

Writing `P_U = compatibleFamilyPresheaf U Y`,
`nestedCoverFamilyNatIso f U Y` is the natural isomorphism

```
P_U ≅ F.op ⋙ P_(N U).
```

Its component at `op c` is `nestedCoverFamilyEquiv f c` converted to an
isomorphism of types; the refinement square proves naturality.
The `hom_app` and `inv_app` projection lemmas expose both component maps.
`nestedCoverFamilyNatIso_gluing` compares these components with the
restriction components of the existing quotient-gluing natural
isomorphisms, using global precomposition by `H_U.symm`.

## Constructed inverse on arbitrary outer covers

Let `c` be any finite full-domain cover of `N U`. No forward-image
condition on `c` is required. The existing inverse functor `G` extends
every component through `e`, restores the target to `d.extendDomain U`
using `extendNestedDomainIso`, then applies the actual inverse
finite-cover localization through `d`. Write
`a = nestedAmbientFiniteCover f c` for this restored ambient cover.
The inverse retains `c.size`, every original component algebra, and
each supplied bounded target restriction. The structural map of its
`i`th component over `d.algebra` is
`(c.map i).restriction.comp U.baseMap`.

`nestedInverseComponentLocusHomeomorph f c i` constructs

```
J_i : ((G.obj c).obj i).locus ≃ₜ (c.obj i).locus.
```

It first uses the actual restricted-domain locus homeomorphism through
`d` into the ambient extended component, then the inverse of the
extended-domain locus homeomorphism through `e`.
`nestedInverseComponentLocusHomeomorph_apply_coe` proves that the
underlying point of `J_i x` is `f.spectrumMap x`. The proof applies
injectivity of `e.spectrumMap`, the extension inverse's spectrum-lifting
equation, and the chart arrow's equation over the original base.

`nestedInverseCoverFamilyEquiv f c` is the explicit composite

```
(e.extendCoverFamilyEquiv c).trans
  (d.restrictExtendedCoverFamilyEquiv a).
```

The intermediate compatible-family types agree definitionally:
restoring the cover target changes no component locus or equality of
underlying base-spectrum points. The reused extension and localization
equivalences prove overlap compatibility and both inverse laws.
This yields

```
S_c : CompatibleFamily c Y ≃ CompatibleFamily (G.obj c) Y.
```

The `val` and `symm_val` projection lemmas expose its actual local maps:

```
(S_c g).val i      = (g.val i).comp J_i,
(S_c.symm h).val i = (h.val i).comp J_i.symm.
```

Thus the arbitrary-cover inverse is implemented by constructed
component homeomorphisms, including the inverse maps, rather than by
assuming a comparison with a cover in the forward image.

## Inverse naturality, gluing and the presheaf comparison

`nestedInverseCoverFamilyEquiv_pullback` proves naturality for every
outer refinement by composing the existing extension and restored
localization refinement squares. The resulting equation is

```
S_b (r.pullback g) = (G.map r).pullback (S_c g).
```

`pullbackEquiv_trans_nestedInverseCoverFamilyEquiv` states this as
an equality of equivalences. The `pullbackEquiv_symm` equation also
compares the gluing-and-restriction inverses of pullback, by injectivity
and the inverse laws as in the forward construction.

`nestedInverseCoverFamilyEquiv_spectrumFamilyMap` identifies the
assembled map on the unchanged disjoint union of actual component
spectra, by composing the extension and localization assembly equations.
`nestedInverseCoverFamilyEquiv_gluingEquiv` gives the global restriction
equation

```
S_c (c.gluingEquiv h) = (G.obj c).gluingEquiv (h.comp H_U).
```

Its component proof uses the underlying-point equation for `J_i` and
subtype extensionality. `glue_nestedInverseCoverFamily` consequently
identifies the actual quotient glue:

```
glue_(G.obj c) (S_c g) = (glue_c g).comp H_U.
```

It applies the preceding restriction equation to the constructed glue
and cancels the existing gluing equivalences.

The entry declaration `nestedInverseCoverFamilyNatIso f U Y` is

```
P_(N U) ≅ G.op ⋙ P_U.
```

The component equivalences and inverse refinement square construct this
natural isomorphism. The `hom_app` and `inv_app` equations expose its
components; `nestedInverseCoverFamilyNatIso_gluing` compares it with
the global restriction components of the quotient-gluing natural
isomorphisms, now using precomposition by `H_U`.

## Family round trips through the actual unit and counit

Let `E = nestedFiniteCoverEquivalence f U`, whose forward and inverse
functors are `F` and `G`.
`nestedInverseCoverFamilyEquiv_nested_unit` proves

```
S_(F.obj c) (T_c g) = (E.unitIso.inv.app c).pullback g.
```

Here the inverse unit is an actual refinement from `G.obj (F.obj c)`
to `c`, so its pullback has precisely the stated direction. The proof
uses its retained identity indices and bounded maps, injectivity of the
component `H`, its inverse law, and the underlying-point formula for
`J_i`.

`nested_nestedInverseCoverFamilyEquiv_counit` proves, for every outer
cover `c`,

```
T_(G.obj c) (S_c g) = (E.counitIso.hom.app c).pullback g.
```

The counit is an actual refinement from `F.obj (G.obj c)` to `c`.
The proof compares component values using the formula for `J_i` and
the inverse spectrum-lifting identity for `H`. Both round trips are
therefore identified through specified refinements of the actual cover
objects.

## Provenance and scope

The registered original is Vladimir Berkovich, *Non-archimedean analytic
spaces* (Trieste lectures, 2009), literature ID
`berkovich-2009-trieste-analytic-spaces`, PDF SHA256
`8cfe4f6f35d5e717ac67c5c8f5ef9ff9185f460bbe5f9a10aeacd84cddeeb2ca`.
Definition 2.2.1 and Exercise 2.2.2(ii), printed/PDF p.9, supply the
full affinoid-domain and arbitrary positive-radius rational-quotient
context. Fact 2.2.3(i) and Definition 2.2.7, printed/PDF p.10, supply
the representing-spectrum and actual domain-embedding context. The
finite affinoid covering convention immediately before Fact 2.2.6 on
p.10 supplies the cover context. Explicit unit generation remains in
force, without an asserted equivalence with absence of common zeros.

All new continuous-family transports, refinement squares, natural
isomorphisms, quotient-gluing comparisons and round-trip equations are
internal consequences of the actual Library constructions. They are
not separately numbered assertions from those pages. This module
reuses `RationalChartDomainNaturality` for the actual nested domain
homeomorphisms, `RationalChartNestedCover` for the cover equivalence,
`RationalChartCoverDescentEquivalence` for inverse localization of
compatible families, and the existing extension, refinement and
quotient-gluing results.

Empty covers and loci, zero algebras, nilpotents and trivial valuations
remain permitted within the chosen-presentation scope. This module
does not construct additional chart identity or composition coherence.
It asserts no algebra or module descent, Tate acyclicity, rational-type
flattening, analytic atlas, or etale or equivariant site.
