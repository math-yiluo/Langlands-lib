# Comparison targets for residue-field values of line-bundle sections

These are precise propositions awaiting a separate proof. They concern
every scheme `X`, every actual locally free rank-one module sheaf
`L : LineBundle X`, and every global section `s` of `L.obj`, all at universe
`u`. No quasi-compactness or separation assumption is imposed.

`LineBundleResidueStalkCriterion` says that at each point `x`, the actual
pulled-back section on `Spec κ(x)` is nonzero if and only if the
section-induced map `𝒪_X → L` is an isomorphism on the underlying
abelian-group stalk at `x`. The left side is exactly
`NonvanishingAt L.obj s x` from `SectionResidue`; it uses the canonical
structure-module comparison, actual module pullback, and evaluation at
one. The right side is the existing `IsStalkFrame` predicate.

`LineBundleResidueOpenComparison` identifies the entire set
`nonvanishingLocus L.obj s` with the underlying set of
`trivializationOpen L.obj s`. This is equality of the full loci; it does
not merely assert the existence of some smaller trivializing neighborhood.
It would imply that the nonvanishing set is open, since
`trivializationOpen` is an open by construction. Combined with the
separately published `maximalTrivialization` theorem, it would also imply
that the section trivializes the bundle on the full nonvanishing open.

`LineBundleSectionResidueComparison` is the conjunction of the two targets.
The general-module theorem `trivializationOpenInterior` only gives the
interior of the stalk-frame set. The present line-bundle target requires
the full set equality, using local rank one. It does not silently replace
an arbitrary set by its interior.

The original reference is Stacks Project Lemma 17.25.10, tag
[01CY](https://stacks.math.columbia.edu/tag/01CY), statement and proof,
in `stacks-invertible-picard-ampleness-2026-10-21`, directory SHA256
`2a0bbd01484fc7cef97110a88cf4b3e472574fbbb9469d037170744a1462f835`,
file `01CY.html`. The source defines the locus by the germ not lying
in `𝔪_x L_x`, proves that the germ is then a basis, and proves openness
and trivialization. The geometric residue-field presentation used here
pulls the section back along `Spec κ(x) → X`. Establishing the
comparison with the stalk-frame condition is part of the proof obligation.
Local rank one is explicit in `LineBundle`, so the local algebra is the
rank-one case over a local ring. The formulation is a derived
scheme specialization and interface for the published constructions.

The source's extra conclusion constructing a section of the inverse
bundle is not part of these targets. Neither tensor powers nor an
ampleness predicate is defined here. No proposition is installed as an
axiom or assumed by either imported construction.
