# Compact Hausdorff spaces of actual nonarchimedean proper-scheme points

This internal construction bundles the actual points of a proper scheme over
a nonarchimedean local field as a compact Hausdorff space, conditional on the
general proper-point assertion. Its application lemmas derive the field
hypotheses of that assertion from `IsNonarchimedeanLocalField`. It uses the original
topology and valuation on an arbitrary field `F : Type u`. It imposes no
characteristic, splitting, projectivity or group hypothesis.

`localField_not_discreteTopology` proves that this original topology is
nondiscrete. If it were discrete, the singleton containing zero would contain
a valuation ball of some nonzero radius `r`. Nontriviality of the valuation
provides a value strictly between zero and one. Surjectivity of the field
valuation realizes its product with `r` as the value of a nonzero field
element. That element lies in the ball, contradicting its containment in the
zero singleton. The proof does not select a replacement norm or topology.

`properSchemePointCompactness_of_localFieldProperty` takes the general
`ProperSchemeLocalPointCompactnessProperty` for every nondiscrete Hausdorff
locally compact topological field. Mathlib's nonarchimedean local-field
instances supply `IsTopologicalDivisionRing` and `LocallyCompactSpace`.
The existing `localField_t2Space` supplies Hausdorffness for the original
topology; the first theorem supplies nondiscreteness. Applying the supplied
property yields compactness of the actual relative point space
`RingPoint F Q F` of any proper scheme `Q` over `F`, with exactly
`schemePointTopology F Q F`. No affineness or projectivity of `Q` is assumed.

`properSchemePointCompactness_of_localFieldProperties` obtains the same
conclusion from the absolute compactness component of
`LocalFieldProperPointProperties`. Universally quantifying its field and scheme
arguments gives exactly the proper-point premise used in the dynamic flag
quotient comparison.

`properSchemePointCompHaus` is the resulting object of Mathlib's `CompHaus`
category. It bundles the actual relative morphism type `RingPoint F Q F`,
equipped with exactly `schemePointTopology F Q F`. The preceding specialization
supplies compactness. Properness of `Q.hom` implies separatedness, and the
published `t2Space_schemePointTopology` supplies Hausdorffness over the
Hausdorff topological field `F`. The construction provides the point space
as a standard compact Hausdorff object for use with continuous maps and
homeomorphisms. The projection lemmas `properSchemePointCompHaus_coe` and
`properSchemePointCompHaus_topology` are reflexive equalities: neither the
point carrier nor its topology is replaced.

The construction and both compactness specializations are conditional on the
general proper-point assertion. This module proves its applicability to the
consumer's local fields, not that assertion or the unconditional
dynamic-parabolic compactness target.
The general proper-point proof and actual dynamic flag quotient existence
remain separate obligations. Provenance is internal: the adapter combines
the existing point statements and field-topology facts without invoking an
additional external structural theorem.
