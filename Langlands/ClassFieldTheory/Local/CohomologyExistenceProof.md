# Local H1 vanishing and H2 invariant existence

Author: Worker 80.

`Langlands.ClassFieldTheory.Local.cohomologyExistence` proves exactly the
published proposition `CohomologyExistence.{u,v}`. For every prime `p`
and every finite extension `F : PadicField.{u} p`, it gives vanishing of
the actual continuous absolute H1 and an additive equivalence from the
actual continuous absolute H2 to `RationalModIntegers`, the quotient Q/Z.
For every finite Galois extension `L/F` with `L : Type v`, it also gives
vanishing of ordinary relative H1 and an injective additive relative H2
map with range `denominatorSubgroup (Module.finrank F.Carrier L)`.
The universes `u` and `v` are independent. The theorem has no additional
mathematical premises.

## Implemented proof

The proof first derives characteristic zero of `F.Carrier` from its
injective scalar map from Q_p. It applies the published
`absoluteInvariantExistence` to obtain a simultaneous family `inv` of
absolute H2 equivalences for the p-adic fields in universe `u`, with the
restriction law given by multiplication by the extension degree.
`absoluteH1Vanishing F.Carrier` supplies absolute H1 vanishing, and
`inv F` supplies the required absolute H2 equivalence.

For a finite Galois extension `L/F` in the independent universe `v`,
`finiteRelativeH1Vanishing F.Carrier L` supplies the relative H1 clause.
For relative H2, the proof embeds `L` into `AlgebraicClosure F.Carrier`.
The image intermediate field `E` lies in universe `u`, and the induced
algebra equivalence `e : L ≃ₐ[F.Carrier] E` transports finite
dimensionality, Galoisness and degree. The existing
`FiniteIntermediateExtension.asPadicField` construction packages `E` as
`EF : PadicField.{u} p`, with its composite Q_p algebra structure.

Algebraic closedness supplies an F-compatible embedding from the
algebraic closure of F into the algebraic closure of E. Its ring map
defines the closure algebra structure; its compatibility with F supplies
the scalar tower. Both the proved absolute inflation exactness and the
degree law apply to this same choice of closure embedding.

The published `absoluteH2InflationExactness F.Carrier E` proves that the
actual `closureInflation F.Carrier E 2` is injective and has range equal
to the kernel of actual absolute restriction to E. Composing that
inflation with `inv F` gives the map
`relativeInvariantFromAbsolute F.Carrier E (inv F)`.
Its imported injectivity lemma applies to the proved inflation
injectivity. Its imported range lemma applies to the proved exactness
and to `hDegree F EF`, with the equivalence `inv EF` on absolute H2 of E.
It identifies the relative image with the subgroup of Q/Z annihilated by
`Module.finrank F.Carrier E`.

Finally, the proof precomposes this map with `relativeH2Equiv e`.
That published equivalence acts on the existing ordinary relative H2
groups, using conjugation of Galois automorphisms and the field map on
units, with descent from cocycles and a proved inverse. Its injectivity
preserves injectivity of the composite. Its surjectivity makes its range
the whole intermediate relative H2 group, so the composite has the same
image in Q/Z. The linear equivalence underlying `e` identifies the two
finite degrees, giving exactly the target denominator subgroup for L/F.

## Dependencies and provenance

This is an internal derived composition of published results. The
arithmetic and continuous-cohomology inputs are imported from
[AbsoluteH1Proof](AbsoluteH1Proof.md),
[AbsoluteInvariantProof](AbsoluteInvariantProof.md) and
[AbsoluteH2InflationProof](AbsoluteH2InflationProof.md). The first of these
also imports [RelativeH1Proof](RelativeH1Proof.md), whose theorem is
applied directly here. The relative construction and its elementary
injectivity and range proofs come from
[RelativeInvariantFromAbsolute](RelativeInvariantFromAbsolute.md).
The universe bridge on actual cohomology comes from
[RelativeH2Transport](RelativeH2Transport.md), and the p-adic field
packaging comes from [ReciprocitySystem](ReciprocitySystem.md).

Worker 80 wrote this assembly and its explanation. Imported results
retain the authorship and source correspondence recorded in their
published pairs. The source correspondence for the target clauses is
recorded in [CohomologyExistence](CohomologyExistence.md). This module
uses those cohomology, field and map definitions unchanged. Its
conclusion is precisely the target existence and vanishing family;
the degree law used in the proof is an input theorem, and no further
normalization, corestriction, fundamental-class or reciprocity law is
asserted here.
