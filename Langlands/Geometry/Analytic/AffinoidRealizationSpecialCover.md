# Specialness and recognition from a finite affinoid realization

This derived construction takes any actual finite chart gluing family `d` in an
indexed affinoid atlas and an `AffinoidRealization c` of that family. It constructs
specialness, recognition of the literal union, a bounded equivalence with the
realized parent algebra, and recovery of its ambient chart. Specialness and the
desired recognized presentation are proved from the realization.

The original-source motivation is Berkovich, *Étale cohomology for
non-Archimedean analytic spaces* (1993), the special-cover definition on printed
page 20 and the recognition criterion and Proposition 1.2.13(ii) on printed
page 21 (PDF pages 17–18). The source is registered as
`berkovich-1993-etale-cohomology`, SHA-256
`06b42aca1c8f237e607d2cf1f15a41fdc9718324a4dc9fd5bce66574254bb91c`.
This module supplies reusable internal infrastructure for that construction;
it does not state the whole proposition.

The field is complete and ultrametric. The ambient topological space and atlas
index have independent universes. The realization includes an actual presented
affinoid algebra `A`, an embedding of its Banach spectrum into the ambient space
with image `d.locus`, full represented-domain maps to every component, their
ambient equations, and compatibility of their entire bounded maps. The full
representation quantifies over all presented affinoid tests. It includes no
specialness witness, tensor admissibility premise, recognized output, or
comparison with the section algebra.

For components `E` and `F` over `A`, `inter_locus_eq_overlapDomain` identifies the
literal locus of their actual pushout intersection with the domain constructed
from the original overlap restriction. The equality follows by taking inverse
images of the gluing family's exact overlap-range equation.

`overlapEquiv` applies `Domain.boundedEquivOfLocusEq` to these full
representations. Its forward map is the restriction of the inverse domain
isomorphism; both directions and their norm bounds are constructed using the
full universal properties. The source algebra is the actual affinoid pushout
of the two component structural maps, and the target is the stored original
overlap algebra.

`leftRestriction_eq` and `rightRestriction_eq` identify both entire original
overlap restrictions with the corresponding pushout leg followed by this
equivalence. Each proof compares two actual inclusions from the overlap domain
to the same component domain. Inclusion uniqueness is proved from the full
represented-domain universal property. On the right, realization compatibility
provides the required structural-map equation. Projecting equality of inclusions
to their bounded restrictions retains every algebra element, including
nilpotents.

`overlapTensorMap_eq` identifies the genuine completed-tensor overlap map with
the actual pushout tensor quotient followed by `overlapEquiv`. The proof uses
completed-tensor uniqueness and the two entire leg identities. The quotient
map is already proved admissible. The bounded inverse of `overlapEquiv` supplies
a bounded right section and therefore proves its forward map admissible.
Composition gives `overlapTensorMap_isAdmissibleEpi`. Admissibility here includes
surjectivity and positive uniform norm bounds for the fiber quotient norm.

`isSpecialCover` combines those overlap admissibility results with Hausdorffness
of the literal union, transported from the parent Banach spectrum through the
realization homeomorphism. Compactness is already proved for every finite chart
gluing family. No Hausdorffness assumption is imposed on the ambient space.

`specialSubset` stores that union and its proved special cover.
`recognizedSubset` applies the existing finite-realization criterion to prove
intrinsic affinoidness of the canonical section algebra, bijectivity of its
canonical spectrum map, and full component representations in the resulting
presentation. Its locus is definitionally `d.locus`.

`recognitionEquiv` has direction
`c.algebra → c.recognizedSubset.algebra`. It composes the constructed parent to
canonical-sections equivalence with the inverse of the intrinsic recognized
presentation's algebra equivalence. It consists of actual algebra maps bounded
in both directions. `recognizedSubset_chart` proves, for every point `x` of the
recognized presentation,

```text
c.recognizedSubset.chart x =
  c.chart (c.recognitionEquiv.spectrumHomeomorph x).
```

The spectrum homeomorphism is contravariant to the displayed algebra
equivalence. The proof invokes the existing chart-recovery theorem for the
unchanged special subset and the supplied realization.

The construction allows trivial valuation, zero algebras, empty families and
nonreduced algebras. It supplies a recognition result for an actual finite
realization. Reverse subatlas recognition, comparisons of full recognized
categories, general equivalent-net invariance, unrestricted analytic morphisms,
analytic sites and Harris specialization remain separate obligations.
