# Actual bounded restrictions between positive-radius rational charts

Author: Worker 56. This module is an internal categorical construction from the
published weighted rational quotients, bounded extension theorem, and spectrum
identification. Its namespace is
`Langlands.Analytic.PresentedAffinoidAlgebra.RationalChart`.

## Actual objects and arrows

Fix an ultrametric normed field `K` and an actual
`A : PresentedAffinoidAlgebra K`. The latter is the existing quotient of a
finite positive-polyradius Tate algebra by a closed ideal, with its constructed
quotient norm. Coefficient completeness is not assumed except where stated
below.

An object `RationalChart K A` retains a finite new-variable arity `m`, an arbitrary
positive real polyradius `s` on `Fin m`, scalar series representatives `g,f j`
over the fixed presentation of `A`, and a proof of
`RationalPresentation.GeneratesUnitIdeal K A g f`. This last condition says
that the actual coefficient classes of `g` and the `f j` generate the unit
ideal of `A`. It is input data, not an assumed map or universal property.

For a chart `d`, `d.algebra` is the already constructed closed quotient

\[
 B_d=K\{r^{-1}T,s^{-1}Y\}/
 \overline{\langle i(I)\cup\{i(g)Y_j-i(f_j)\}_j\rangle},
\]

where `r = A.polyradius`, `I = A.ideal`, and `i` includes the old variables.
The bounded structural homomorphism is `d.baseMap : A → B_d`. The set
`d.locus` is the actual subspace of `BanachSpectrum A` defined by

\[
 V_d=\{x\mid x(\bar f_j)\leq s_j x(\bar g)\text{ for every }j\}.
\]

The definitions `spectrumMap` and `locusHomeomorph` reuse the existing continuous
structural spectrum map and the proved homeomorphism `M(B_d) ≃ₜ V_d`.
`locusHomeomorph_apply_coe` records that its underlying base-spectrum point is
that structural image.

A morphism `d ⟶ e` has the space direction and consists of an actual
`BoundedAlgHom K B_e B_d` named `restriction`, together with the equation
`restriction.comp e.baseMap = d.baseMap`. Neither existence nor boundedness of
this map is assumed merely from an inclusion of loci. The identity uses the
actual identity algebra map. Composition uses composition of the actual
bounded maps in the reverse algebra direction; the over-base equations compose.

`Restriction.ext` reduces equality to equality of these bounded maps. The
`Subsingleton (Restriction d e)` instance applies the published
`RationalPresentation.hom_ext_base` to the source algebra `B_e`, using the unit
ideal generation stored by `e`. Both candidate maps have the same restriction
to `A`. The imported extensionality theorem proves their equality, rather than
assuming it as part of the chart. The category laws then follow from this
uniqueness. Thus the category is thin, with objects still retaining all the
chosen presentations and coefficients.

## Spectrum realization

For an actual arrow `h : d ⟶ e`, `h.spectrumMap` pulls bounded multiplicative
seminorms back along its bounded algebra homomorphism. The theorem
`spectrumMap_over_base` proves the structural square

\[
 i_e^*\bigl(h^*(x)\bigr)=i_d^*(x)
\]

by evaluating the stored algebra-map equation on every base element.
`Restriction.subset` derives `V_d ⊆ V_e`: lift a point of `V_d` through
`d.locusHomeomorph.symm`, apply `h.spectrumMap`, and use the structural square
and the target homeomorphism. `locusMap` is the resulting continuous subtype
inclusion. It preserves the underlying point of `M(A)`.

`locusHomeomorph_naturality` identifies the spectrum pullback with that inclusion
under the two homeomorphisms. Its proof is subtype extensionality and the same
structural square. `isClosedEmbedding_spectrumMap` proves injectivity by mapping
two points to the base and using injectivity of `d.locusHomeomorph`; continuity,
compactness of the source spectrum, and Hausdorffness of the target then give a
closed embedding.

`toAffinoidSpace` sends a chart to the existing presented affinoid space
`Opposite.op d.algebra` and an arrow to its actual opposite bounded map.
`toTopologicalSpace` composes this with the existing affinoid spectrum functor.
`locusFunctor` sends a chart to `TopCat.of d.locus` and an arrow to `locusMap`.
The definition `spectrumLocusIso` assembles the constructed homeomorphisms into
a natural isomorphism of these two functors. Its naturality proof is exactly
`locusHomeomorph_naturality`.

## Constructed arrows and presheaves

`withRadii d t` retains the rational coefficients and unit-generation proof,
changing just the displayed positive radii. If `t j ≤ d.radii j` for every
coordinate, `radiusRestriction` constructs `d.withRadii t ⟶ d` with the published
bounded `radiusMap`. Its over-base equation follows from `radiusMap_baseMap`.
This arrow requires no completeness assumption.

Over a complete coefficient field, `restrictionOfFractions d e b hb heq`
constructs an arrow from explicit fraction values `b j : B_d`. The hypothesis
`hb` is the existing weighted bounded-monomial condition at the target chart's
radii, and `heq` is the equation

\[
 d.\mathrm{baseMap}(\bar g_e)b_j=
 d.\mathrm{baseMap}(\bar f_{e,j}).
\]

Completeness of `K` supplies completeness of the actual quotient `B_d` through
the published Banach construction. `liftFromBase` then performs weighted
evaluation and closed-relation descent. Its proved base identity gives the
arrow equation, and `restrictionOfFractions_fraction` records that the resulting
map takes each target fraction coordinate to the prescribed `b j`. The
bounded-monomial condition remains an explicit hypothesis.

`boundedPresheaf` is the contravariant functor assigning each chart its actual
`PresentedAffinoidAlgebra K` and each opposite arrow its bounded restriction.
`banachPresheaf`, over complete `K`, composes it with the published functor to
`BanachRing`; it retains the actual complete normed quotient rings and bounded
ring maps. `algebraPresheaf` retains their actual commutative `K`-algebras in
`CommAlgCat K`. The functor laws follow from the definitions of identity and
composition. Finally, `baseMapNat` is a natural transformation from the constant
base-algebra presheaf to `boundedPresheaf`; naturality is the stored over-base
arrow equation.

## Provenance and scope

The original context is Vladimir Berkovich, *Non-Archimedean analytic spaces*,
Trieste lectures (2009), registered as
`berkovich-2009-trieste-analytic-spaces`, PDF SHA256
`8cfe4f6f35d5e717ac67c5c8f5ef9ff9185f460bbe5f9a10aeacd84cddeeb2ca`.
Exercise 2.2.2(ii), printed/PDF page 9, supplies the common-denominator rational
quotient and positive-radius inequalities. Fact 2.2.3(i), page 10, gives the
spectrum/image identification context; Definition 2.2.7, page 10, defines the
category of affinoid-domain embeddings. These pages were read directly.

The chosen-chart category, its actual-map uniqueness, natural spectrum/subspace
identification, and quotient-algebra presheaves are internal derivations from
the published concrete constructions, with their proofs described above. The
explicit unit-ideal hypothesis is retained; no equivalence with the source's
no-common-zero condition is proved here. In particular, the full
image-containment factorization property in Definition 2.2.1, page 9, remains
separate. No converse construction of an arrow from an arbitrary locus inclusion,
Grothendieck topology, sheaf condition, analytic atlas, etale site, or equivariant
site is asserted.

All arities may be zero, radii need not lie in a value group, and neither
nontrivial valuation nor reducedness is imposed. The unit ideal and zero
quotients remain allowed. The module works with chosen presentations, not a
proof of independence from arbitrary affinoid presentations.
