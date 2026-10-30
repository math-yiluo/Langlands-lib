# Actual affinoid atlases on induced rational spectra

Author: Worker 36.

The module constructs an `IndexedAffinoidAtlas` on the actual balanced
quotient of a rational quotient spectrum by an open subgroup. It uses
the actual quotient algebras, the published radius-one algebra comparison,
the constructed coset homeomorphism, and the accompanying disjoint-atlas
transport. No analytic structure of the resulting quotient is assumed.

## Sources and provenance

Berkovich's unfinished *Etale equivariant sheaves on p-adic analytic
spaces*, retained Equish_1996 manuscript (1995–1996), Construction 1.1.2,
printed/PDF page 2, constructs induction from an open subgroup as a
disjoint union of copies indexed by left cosets. Its rule for the action
uses `g*gi = gj*h`. The present module supplies the actual affinoid atlas
for the previously constructed balanced rational-spectrum model of those
copies.

Registered source folder:
`provided-7bb3903652336bd799aad8853b8efd7ff3bcc0c7652745417f4745a14ac08e90`,
SHA256 `e046cadfb9dcec4b0cf6624f80d6316bf532416153b82023f5100bd1ab0726cd`.
Its member *Berkovich--Etale equivariant sheaves on p-adic analytic spaces
(unfinished manuscript)--1996.pdf* has SHA256
`91567a75866a27cbe6690b6f075693df5afaa02524223d94d52ea37d77bb6637`.
The manuscript is unfinished.

The atlas obligations are those of Berkovich, *Étale cohomology for
non-Archimedean analytic spaces* (1993), section 1.2, Definition 1.2.3
and Remark 1.2.4(i), printed page 16 / PDF page 13.
Registered source: `berkovich-1993-etale-cohomology`, PDF SHA256
`06b42aca1c8f237e607d2cf1f15a41fdc9718324a4dc9fd5bce66574254bb91c`.
They use a compact net, actual affinoid chart algebras and bounded
domain restrictions with composition.

The radius-one comparison specializes the strictness clause of
Berkovich, *Non-archimedean analytic spaces* (Trieste lectures, 2009),
Definition 2.1.2, printed/PDF page 7. The inherited full affinoid-domain
factorization uses Definition 2.2.1, page 9, including all affinoid
test spaces. Registered source:
`berkovich-2009-trieste-analytic-spaces`, PDF SHA256
`8cfe4f6f35d5e717ac67c5c8f5ef9ff9185f460bbe5f9a10aeacd84cddeeb2ca`.
These original passages were read for this construction. No source-specific
errata note was present in the current Library.

The rational-spectrum specialization, the combination of the two
homeomorphisms and the chart formulas are derived constructions, not
independently numbered claims in the sources. The implementation imports
the published actual quotient, bounded equivalence, induced charts and
disjoint atlas by Lean name.

## Actual algebras and homeomorphisms

The namespace is
`Langlands.Analytic.StrictTestDomain.RationalAutomorphism.RationalSpectralAction.OpenSubgroupTransport`.
The hypotheses are a complete ultrametric normed field `K`, an actual
presented strict affinoid algebra `P`, a topological group `G`, a
`RationalSpectralAction G P` and its object `X`. The coefficient and
group universes are independent. Write `H` for `X.subgroup`.

`X.domain.obj.algebra` is the existing actual strict rational
closed-ideal Tate quotient. `X.LocalSpectrum` is its actual bounded
multiplicative spectrum with the previously constructed subgroup
action. `X.InducedSpectrum` is the actual balanced quotient
`G ×_H X.LocalSpectrum`, with its quotient topology and continuous
full-group action. None of these carriers is replaced by an arbitrary
space.

`inducedChartAlgebra` is
`PresentedAffinoidAlgebra.ofStrict K X.domain.obj.algebra`.
This is a finite positive-polyradius quotient presentation with radii
one and ideal pulled back through the coefficient-preserving
radius-one isometry. The imported comparison is an actual bounded
algebra equivalence preserving the quotient norm.
`localAffinoidSpectrumHomeomorph` is its contravariant spectrum
homeomorphism

`X.LocalSpectrum ≃ₜ BanachSpectrum X.inducedChartAlgebra`.

`inducedAffinoidFamily` assigns that algebra to every left coset.
`inducedAffinoidCopiesHomeomorph` sends `(c,x)` in the disjoint
sum of its spectra to
`(c, X.localAffinoidSpectrumHomeomorph.symm x)`.
The inverse applies the forward local comparison. The two inverse
equations follow from its inverse equations on the second coordinate;
continuity in each direction is proved on each topological summand.

`inducedAffinoidHomeomorph` composes this with the published
`inducedCosetHomeomorph`. Its proved formula is

`(c,x) ↦ X.inducedChart c.out
  (X.localAffinoidSpectrumHomeomorph.symm x)`.

Here `inducedChart a y = [a,y]` is the actual balanced-quotient chart.
The chosen representative of the identity coset need not be `1`;
the distinguished unit chart remains the existing `inducedChart 1`.

## Constructed atlas and chart domains

`inducedAffinoidAtlas` applies
`DisjointAffinoidAtlas.transportAtlas` to this actual quotient family
and the constructed homeomorphism. Its indices are precisely cosets
whose chart spectrum is nonempty; there is no nonemptiness or
finite-index hypothesis. Empty local spectra give an empty atlas on
the empty induced space.

The chart algebra is `inducedChartAlgebra` at every such index.
`inducedAffinoidAtlas_chart` records the same formula as the
homeomorphism, restricted to that chart spectrum.
`range_inducedAffinoidAtlas_chart` proves its range is exactly the
range of `X.inducedChart c.val.out`. One inclusion uses the inverse
local comparison; the other applies its forward comparison and cancels
the inverse. The existing quotient-chart fiber formula then proves
`range_inducedAffinoidAtlas_chart_eq_fiber`: the domain is exactly
the fiber `X.inducedComponent ⁻¹' {c.val}`. The chart embedding uses
the actual subspace topology.

The transport constructor proves local Hausdorffness, injective domain
indexing and the net condition. Chart compactness follows from the
compact quotient spectra. It supplies every required bounded
restriction, its spectrum inclusion and unique factorization on all
presented affinoid tests, including arbitrary positive polyradii.
Its stronger factorization is valid for every normed commutative test
algebra. Identity and composition are equalities of bounded algebra
maps.

`inducedAffinoidAtlas_index_eq_of_subset` uses the transport's
nonempty-component containment result. Since this family is constant
as an algebra family, `inducedAffinoidAtlas_restriction_eq` identifies
each restriction literally with the bounded identity on
`inducedChartAlgebra`: after equating the two indices the defining
restriction reduces to that identity.

## Scope

This unit constructs the affinoid atlas on the actual induced rational
space. It does not yet promote the existing full-group action or
transport arrows to compatible bounded maps for every pair of these
chosen atlas charts. Those further maps must include the subgroup
operator caused by the choice of coset representatives. General
refinements and analytic morphism localization, structure sheaves,
etale and quasi-etale sites, the full analytic induction universal
property and Harris's tower specialization remain host-task obligations.
