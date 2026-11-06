# Section recovery from an actual finite affinoid realization

Author: Worker 36.

This module constructs a full bounded equivalence between a given actual
affinoid presentation and the Banach section equalizer of finitely many
original charts that form a full affinoid-domain cover of that presentation.
The presentation need not be an original chart of the ambient atlas.
The inverse bounded maps and the canonical spectrum-map identification
are proved from actual finite full-domain descent.

The source motivation is Berkovich, *Étale cohomology for non-Archimedean
analytic spaces* (1993), the finite Banach equalizer and canonical spectrum
map following Lemma 1.2.12, printed pp.20–21 / PDF pp.17–18, and the
recognition conditions and Proposition 1.2.13(ii) on printed p.21 / PDF p.18.
Registered source `berkovich-1993-etale-cohomology`, SHA256
`06b42aca1c8f237e607d2cf1f15a41fdc9718324a4dc9fd5bce66574254bb91c`.
Those original pages were read for this unit; no source-specific errata
file was found in the available project and Library locations.

This is a derived extension of the existing original-parent recovery
construction to any supplied actual affinoid realization of the finite
cover. It does not assume a section-algebra comparison or construct a new
affinoid structure on an arbitrary finite union.

Fix `d : FiniteChartGluingData a`. Its components and represented pairwise
overlaps are actual original charts of `a`. Its `SectionAlgebra` is the
existing closed compatible-tuple subalgebra of the finite product, with
its inherited Banach norm. `d.AffinoidRealization` packages the precise
input data for recovery:

- an actual finite closed weighted Tate presentation `algebra = A`;
- a continuous embedded chart from its genuine Banach spectrum to `X`,
  with range exactly `d.locus`;
- bounded maps from `A` to each unchanged component algebra, recovering
  the corresponding original ambient chart;
- the full represented-domain universal property of each component at
  its literal relative locus in the spectrum of `A`;
- equality of both entire bounded composites from `A` to every original
  overlap algebra.

The last condition is compatibility of the supplied local algebra maps.
It is not inferred from their action on spectrum points. The output
bounded section-algebra equivalence and its inverse are absent from these
input data. Neither a sheaf comparison nor maximal recognition is supplied.

`componentDomain` uses the unchanged component algebra and its full
representation. `domainCover` constructs a `Domain.FiniteCover` of the
whole presentation `A`. Coverage follows by applying the chart range
equality to a spectrum point and finding a component of the finite union.

`overlap_represents` composes a component's full representation with the
actual original atlas restriction from the overlap. The represented locus
is exactly the inverse image of the original overlap range. The proof uses
the original overlap chart's spectrum points, the supplied chart formulas
and injectivity of the parent chart to identify this locus.
`overlapDomain` retains that original overlap algebra and the complete
bounded composite through the first component.

`projection_compatible` proves compatibility of the equalizer projections
after every actual full-domain test into two cover components. Such a test
factors through the just constructed overlap domain by its literal image.
The supplied bounded overlap compatibility gives the second structural
triangle; thinness of actual full-domain inclusions identifies both
component restrictions with the composites through this overlap.
The equalizer's full bounded projection equation then gives the required
test equality.

`glueToParent` applies finite full-domain bounded-map descent to those
projections, constructing the entire bounded map from `d.SectionAlgebra`
to `A`. The imported descent construction uses scalar gluing through an
actual finite rational refinement and a proved inverse restriction norm
bound, so this map retains the original Banach algebra norms.
`restriction_comp_glueToParent` recovers every original projection as an
equality of bounded maps.

In the other direction, `restrictFromParent` lifts the supplied compatible
bounded family into the actual equalizer. Its projection formula is
definitional. `glueToParent_restrictFromParent` uses finite-cover algebra
separation, and `restrictFromParent_glueToParent` uses equalizer coordinate
extensionality. Both identities hold on all algebra elements.
`sectionAlgEquiv` bundles these constructed bounded maps and inverse
identities. No faithfulness of spectrum points is used to recover algebra
elements or maps.

`locusHomeomorph` identifies the literal union with the original parent
spectrum through the supplied embedded chart and exact range equality.
Its component formula is the comap of the original bounded component map.
`spectrumMap_eq_parent` identifies the existing canonical equalizer
spectrum map with the composite of this homeomorphism and the inverse
spectrum homeomorphism of `sectionAlgEquiv`. The proof reduces to a
component using the proved surjective finite disjoint-union map, then
evaluates the full bounded projection-recovery identity.
`spectrumHomeomorph` and its value formula consequently realize the
canonical point map as a homeomorphism; `bijective_spectrumMap` proves
bijectivity of that exact existing map.

`isAffinoid_sectionAlgebra` proves intrinsic affinoidness of the unchanged
Banach equalizer. It transports the actual admissible finite Tate quotient
of `A` through the constructed bounded equivalence, using the proved
bounded inverse and norm-controlled quotient construction.

`originalAffinoidRealization` constructs all input fields when the finite
union is an original chart. It uses the existing original restrictions,
their full representation theorem, ambient formulas and bounded overlap
compatibility. Thus the generalized input has a concrete constructed
instance from the existing geometry, rather than an assumed comparison.

The coefficient field, ambient-space and original-index universes are
independent. The field is complete and ultrametric, including trivial
valuations. The ambient space need not be Hausdorff; the parent chart gives
the required subspace topology. Empty covers and zero or nonreduced
algebras remain allowed.

This unit proves section recovery from the stated full component data.
It does not construct those data for every new recognized-chart domain,
prove specialness or tensor admissibility of arbitrary finite covers,
transfer all three recognition conditions to arbitrary new special subsets,
or prove maximal closure or idempotence. The special-intersection statement
and closed-ideal effectiveness are not assumed. These remaining geometric
instantiations are distinct from the proved algebraic recovery.
