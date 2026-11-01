# Original-chart domain sites under finite relative local refinement

Author: Worker 36.

This module compares the actual original-chart domain sites of two supplied
affinoid atlases on the same topological space.
Mutual finite relative local refinement is required. The comparison retains
literal subsets, their inclusion order, and every quasinet covering sieve.
It induces an equivalence of sheaf categories with arbitrary category-valued
coefficients. A locally refining selection of the original charts is the
concrete specialization.

The source conventions are Berkovich, *Étale cohomology for
non-Archimedean analytic spaces* (1993), §1.1, printed pp.13–14 / PDF
pp.10–11; Definition 1.2.3 and Remark 1.2.4(i), printed p.16 / PDF p.13;
Definition 1.3.1, printed p.23 / PDF p.20; and the G-topology paragraph,
printed p.25 / PDF p.22. Registered source:
`berkovich-1993-etale-cohomology`, SHA256
`06b42aca1c8f237e607d2cf1f15a41fdc9718324a4dc9fd5bce66574254bb91c`.
All these original pages were read for this unit. No source-specific errata
file was found in the available project and Library locations.

The result is derived from the published finite relative refinement
calculus in `AtlasTopology.Refinement`, the actual original-subatlas
construction in `AtlasSubatlas`, and the domain topology in
`OriginalDomainTopology`. It is not asserted as a
separately numbered source theorem. The two supplied atlases need not have
the same chart-index universe. The ambient space and coefficient field are
shared. The comparison does not assert compatibility of their bounded
algebra structures.

`IsOriginalChartDomain.of_locallyRefines` restricts a finite relative
local refinement to an actual domain S and refines its contained-chart
quasinet. Thus S is a domain of the refining atlas. This direction requires
only one refinement. `OriginalChartDomain.transport` retains S's literal
carrier with the resulting domain proof. Mutual refinement supplies
both transports for `refinementOrderIso`. Set extensionality proves its
inverse laws, and its order comparison is literal subset inclusion.
`refinementEquivalence` is the resulting equivalence of inclusion
categories. No new affinoid algebra or global analytic object is assumed
among the refinement hypotheses.

For an arbitrary sieve, `sieveFamily_functorPullback_refinement` proves
that its pullback has exactly the same family of source subsets.
Transporting a source domain in the reverse direction and applying the
domain roundtrip supplies the nontrivial inclusion of families. The
thin inclusion categories make the containment-arrow proofs irrelevant.
`functorPullback_mem_quasinetTopology_iff` then identifies the full finite
relative neighborhood covering conditions. This uses equality of the
subset families, rather than only point coverage.

The instances `refinementFunctor_isCocontinuous` and
`refinementInverse_isCocontinuous` follow from that exact covering
criterion. Mathlib's `Equivalence.isDenseSubsite_inverse_of_isCocontinuous`
provides the dense-subsite instance, and `Equivalence.sheafCongr`
constructs `refinementSheafEquivalence`. Its coefficient category C is
arbitrary; no sheafification or limits assumption is needed.
`refinementSheafEquivalence_obj_obj` identifies the value of the forward
transport at a domain with the original sheaf's value at that same
actual subset, transported back to the first atlas.
`ofArrows_refinement_mem_iff` also proves the generated-family criterion
directly by the equality of actual carriers. Its family-index universe
is arbitrary, including empty families and empty domains.

For a locally refining original subatlas selection P, the supplied
refinement gives one direction. Inclusion of its chart family in the
original chart family gives the other. The declarations
`isOriginalChartDomain_subatlas_iff`, `originalDomainSubatlasOrderIso`
and `originalDomainSubatlasSheafEquivalence` specialize the preceding
constructions. No downward-closure or upper-cofinality assumption on P
is used. The subatlas retains the original algebras and bounded
restrictions through the imported construction; the new site comparison
operates on its actual domain subsets.

This concerns the existing fixed-original-chart domain sites, whose
domains use only charts of the supplied atlas. It does not construct a
saturated affinoid atlas, prove invariance under arbitrary atlas
quasi-isomorphisms, identify structure sheaves, prove arbitrary-cover
descent for full strong morphisms, or construct the analytic étale site.
Mutual refinement is substantive: point coverage of chart families alone
is insufficient.
