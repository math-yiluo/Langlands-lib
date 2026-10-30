# Continuous finite-cover gluing under bounded base equivalences

Worker 56 constructs transport of compatible continuous families along the
actual component locus homeomorphisms induced by a bounded equivalence of
ambient presented affinoid algebras. The construction gives an equivalence
with an explicit inverse and commutes with restriction and continuous gluing.

The declarations are in
`Langlands.Analytic.PresentedAffinoidAlgebra.Domain.FiniteCover`.

## Inputs and provenance

The coefficient field `K : Type u` is complete and ultrametric. The ambient
algebras `A` and `B` are actual presented affinoid algebras: finite
positive-polyradius Tate algebras modulo closed ideals, with their quotient
norms. A full domain retains a representing algebra, its bounded structural
map, its closed locus in the actual bounded multiplicative-seminorm
spectrum, the exact spectrum image, and universal factorization against
all presented affinoid tests.

The published `DomainCoverBaseTransport` takes a finite full-domain cover
`c` of `V` and a bounded algebra equivalence `e : BoundedAlgEquiv K A B`
to a cover `c.transportBase e` of `Domain.transportBase e V`.
It keeps every component index, quotient algebra and bounded restriction.
Its component and target loci are transported by the preimage under
`e.spectrumHomeomorph`, and
`Domain.transportBaseLocusHomeomorph` restricts this actual spectrum
homeomorphism to each domain locus.

The published `DomainCoverDescent` supplies `CompatibleFamily c Y`,
the subtype of families of continuous maps on the component loci that
agree at equal underlying ambient spectrum points. Its imported
`DomainGluing` constructs gluing using the quotient map from the finite
disjoint union of actual representing spectra. The target `Y : Type v`
has a universe independent of `u`, with only a topological-space
structure and no separation or compactness hypothesis.

The imported domain definition is Berkovich, *Non-archimedean analytic
spaces* (Trieste lectures, 2009), registered source
`berkovich-2009-trieste-analytic-spaces`, PDF SHA256
`8cfe4f6f35d5e717ac67c5c8f5ef9ff9185f460bbe5f9a10aeacd84cddeeb2ca`,
Definition 2.2.1, printed/PDF p.9; Definition 2.2.7 on p.10 supplies the
domain embedding context. Transport of compatible continuous families and
the gluing square are internal consequences of the published constructions,
rather than separately named theorems from the source.

## Family transport and its inverse

`transportBaseFamily c e g` has component `g i` composed with
`Domain.transportBaseLocusHomeomorph e (c.obj i)`. Its source is the
transported component locus, and its target is `Y`.
`transportBaseFamilyInverse` composes a family on the transported cover
with the inverse component homeomorphisms. Both constructions retain
the exact component index.

`compatible_transportBaseFamily` applies the ambient spectrum
homeomorphism to an equality of transported ambient points, then uses
the original family's compatibility. In the inverse direction,
`compatible_transportBaseFamilyInverse` applies the inverse ambient
homeomorphism. The component homeomorphisms are restrictions of these
ambient maps, so the obtained equalities are precisely the ones needed
by compatibility.

`transportBaseFamilyInverse_transportBaseFamily` and
`transportBaseFamily_transportBaseFamilyInverse` prove both family
inverse laws by function and continuous-map extensionality and the
component homeomorphism inverse laws. The entry
`transportBaseFamilyEquiv` bundles these maps and the proved compatibility
as an equivalence of compatible-family types. Its inverse is constructed
componentwise; no output equivalence is assumed.
`transportBaseFamilyEquiv_apply` exposes its pointwise formula.

## Restriction, gluing and actual spectra

`transportBaseFamily_restrict` proves that transporting the restrictions
of a global continuous map `f` gives the restrictions of `f` composed
with the target locus homeomorphism. The proof uses the published
naturality of that homeomorphism with the actual bounded component
restrictions. `transportBaseFamilyEquiv_gluingEquiv` is the corresponding
commuting square for compatible-family equivalences and the concrete
global gluing equivalences.

`glue_transportBaseFamily` proves that gluing a transported compatible
family equals the original glued map composed with the target locus
homeomorphism. Uniqueness of gluing on the transported cover reduces
the equation to its restrictions. The preceding restriction identity
and the original restriction-of-gluing law prove each component
equation. Thus this comparison concerns the actual quotient-lift
gluing maps.

`transportBaseFamily_spectrumFamilyMap` proves equality of the two
continuous maps assembled on the disjoint unions of actual component
spectra. These disjoint unions are definitionally the same, since the
quotient algebras are retained. The equality follows from the published
comparison between each transported quotient-spectrum map and its
component locus homeomorphism; it holds for every family, even before
assuming compatibility.

`transportBaseFamily_postcomp` proves that family transport commutes
with each continuous map `p : C(Y, Z)`, by pointwise composition.
The universe `w` of `Z` is independent of both `u` and `v`.

The construction allows zero cover size, empty loci, zero quotient
algebras, arbitrary finite positive polyradii and trivial valuation.
It requires an actual bounded equivalence of the ambient algebras.
It constructs transport and gluing for continuous maps on supplied
represented loci. Algebra-section descent, pullbacks along arbitrary
analytic morphisms, rational-domain existence, analytic structure
sheaves, atlas completion and etale sites remain separate obligations.
