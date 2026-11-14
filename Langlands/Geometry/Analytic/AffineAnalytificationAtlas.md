# The affinoid atlas and localization of a finite polynomial locus

This construction equips `AffineAnalytification.Space K P` with an actual
affinoid atlas, saturates it using full affinoid domains and gives an object
of the Library's existing localized saturated-atlas category. It allows
arbitrary finite polynomial presentations, including zero variables, zero
algebras and nonreduced algebras.

## Provenance

The polynomial-locus construction is derived from Berkovich, *Spectral
Theory and Analytic Geometry over Non-Archimedean Fields* (1990),
Definition 1.5.1 and Remark 1.5.2(i), printed p.19/PDF p.33, and the proof of
Theorem 3.4.1, steps (1)--(3), printed p.64/PDF p.78. The registered source
is `provided-a03a0182668f6b92b01deacac09a9992b3edf55e23a0a2194554384ae44bd8d4`,
SHA256 `9b543e7ffae8ec6febf154a60c4d11a288f7ecc3795c66f004ba3200a6824e79`.

The net of affinoid charts follows Berkovich, *Étale cohomology for
non-Archimedean analytic spaces* (1993), Definition 1.2.3, printed p.16/PDF
p.13. The passage to full-domain saturation and the existing localization
uses the Library implementations motivated by Definition 1.2.7 and
Proposition 1.2.8, printed p.18/PDF p.15. The registered source is
`berkovich-1993-etale-cohomology`, SHA256
`06b42aca1c8f237e607d2cf1f15a41fdc9718324a4dc9fd5bce66574254bb91c`.
The least-index selection and the explicit bounded comparisons below are
derived implementation choices, not separate numbered assertions of the
sources.

## Hypotheses and actual domain comparisons

All definitions lie in `Langlands.Analytic.AffineAnalytification`. The field
`K` is complete, nontrivially normed and nonarchimedean. The input
`P : FinitePolynomialPresentation K A` is an actual finite-variable
polynomial surjection onto a commutative `K`-algebra. No norm on `A`,
positive-arity hypothesis or nonemptiness hypothesis is required. The
preceding gluing module supplies `algebra K P m`, the actual closed-kernel
quotient, `restriction K P h` for `h : m ≤ k`, and its chart in `Space K P`.

`chainDomain K P h` regards the smaller original quotient as a full
affinoid domain of the larger one through that actual restriction. The
proved representation tests every presented affinoid algebra, including
nonreduced tests. `chainDomain_locus` identifies its represented locus with
the preimage of the smaller global chart range under the larger chart.
Its proof uses the compatibility of chart maps with restrictions and the
injectivity of the larger chart.

For an equality of two global chart ranges, `equalRangeEquiv K P h`
compares their actual algebras over the chart at the maximum of the two
indices. The two full domain representations have equal loci there.
`Domain.boundedEquivOfLocusEq` constructs bounded maps in both directions
from their universal properties and proves both inverse identities.
`equalRangeEquiv_comp_restriction` and its symmetric version record the
equations over this common larger algebra.
`equalRangeEquiv_algebraMap` proves compatibility with the explicit maps
from `A`, by evaluating the common-base equation on the image of an element
of `A` and using the original restriction laws. Thus this comparison is
an algebra construction, rather than an identification of algebras from
their points.

## Selecting an atlas without distinct-radius assumptions

The Library's `IndexedAffinoidAtlas` requires indices to map injectively
to chart ranges. Polynomial loci can have repeated ranges even when the
radii increase strictly, so the original natural indices do not always
meet this requirement.

`ChartIndex K P` consists of the original natural indices which are least
among those with the same range. `representative K P m` uses `Nat.find`
on the nonempty set containing `m` itself. `range_representative` proves
that its range is the original range, and `representative_le` records its
minimality relative to `m`. `representativeEquiv K P m` recovers the
actual algebra of each original chart from the selected representative
through the bounded equivalence just constructed.

`selected_chartDomain_injective` uses minimality in both directions.
`selected_range_subset_iff` proves that an inclusion between selected
chart ranges is equivalent to the corresponding inequality of their
original indices. If the indices had the opposite order, monotonicity of
the original ranges would give equality, and minimality gives the required
inequality.

`selected_isNet` proves both net conditions. A point in the `m`-th chart
has the next original chart as a neighborhood; that chart range occurs
in the selected family through its representative. Intersections are
the original chart range at the minimum of the two indices, which also
occurs through its representative. Its preimage in the intersection
is the whole intersection, providing the required local net there.
Empty ranges cause no difficulty: the local point obligations on an
empty intersection are vacuous, and all equal empty ranges have a
single selected representative.

`atlas K P` keeps the original algebra and chart of each selected index.
Every chart-domain inclusion uses `selected_range_subset_iff` to select
the existing actual radius restriction. The chart equation follows from
the gluing equation. The full universal property follows from
`represents_restriction`, converting global chart-range containment to
containment in the larger chart's spectrum by chart injectivity.
Identity and composition are the proved identities of the actual
bounded algebra maps. Local Hausdorffness follows from the preceding
Hausdorff-space construction. `atlas_hasDirectedCharts` represents the
chart at the maximum index in the selected family.

## Presentation and localization

`presentation K P : AffinoidAtlasPresentation.{u,u,0} K` is this atlas on
the literal space `Space K P`. The algebra `A` may have a different
universe; the analytic space and its chart algebras remain in the
universe of `K`.

`saturated K P : SaturatedAtlasPresentation.{u,u,u} K` applies the
Library's `SaturatedAtlasPresentation.ofSaturation`, constructing all
local full affinoid domains. `localized K P` applies its existing
`localizationFunctor` to obtain an object of
`SaturatedAtlasPresentation.LocalizedCategory`. No alternative analytic
category or assumed analytification input is introduced.
`saturated_space` and `localized_space` record that both constructions
retain the literal glued topological space.

The quotient algebras, their restrictions and their full universal
properties remain part of the analytic structure throughout. Selecting
one representative of a repeated range neither radicalizes its ideal
nor discards its nilpotents; the explicit bounded comparisons also
recover every omitted original algebra.

## Scope

The genuine `Spec A` and affine finite-type scheme interfaces, including
global-section algebra and affine scheme isomorphism, are supplied by
the scheme construction unit. General independence of presentation,
functoriality for all affine scheme morphisms, rational-point and
point-topology comparisons, the scheme analytification universal
property and arbitrary analytic field-extension comparisons remain
subsequent proposition and proof tasks. The present atlas construction
does not prove that final analytification bridge.
