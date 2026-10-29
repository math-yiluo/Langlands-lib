# Concrete disjoint affinoid atlases

Author: Worker 36.

The module constructs an affinoid atlas on the actual topological disjoint
union of the spectra of a family of finite positive-polyradius quotient
algebras. Every chart restriction and its domain factorization are constructed
from this family. The input includes neither an atlas nor a factorization
property of the resulting space.

## Sources and provenance

The original atlas definition is Berkovich, *Étale cohomology for
non-Archimedean analytic spaces* (1993), section 1.2, Definition 1.2.3,
printed page 16 / PDF page 13. It assigns an affinoid algebra and a spectrum
homeomorphism to each member of a compact net on a locally Hausdorff space.
For every containment of net members it requires a bounded algebra map
identifying the smaller chart with an affinoid domain of the larger one.
Remark 1.2.4(i) on that page records composition of restrictions.
Registered source: `berkovich-1993-etale-cohomology`; PDF SHA256
`06b42aca1c8f237e607d2cf1f15a41fdc9718324a4dc9fd5bce66574254bb91c`.

The affinoid-domain condition is the universal property in Berkovich,
*Non-archimedean analytic spaces* (Trieste lectures, 2009),
Definition 2.2.1, printed/PDF page 9. Its test objects are all affinoid
spaces, without a strictness restriction. The condition includes a closed
image and unique factorization of every morphism whose image lies in the
domain. Registered source: `berkovich-2009-trieste-analytic-spaces`; PDF
SHA256 `8cfe4f6f35d5e717ac67c5c8f5ef9ff9185f460bbe5f9a10aeacd84cddeeb2ca`.
Both cited passages were read in the originals. No corresponding erratum
was found in the available project notes.

The indexed record and the concrete disjoint-union implementation are
derived constructions, rather than a separately numbered result in these
sources. The derivation uses the published topology of actual bounded
multiplicative spectra and the published quasinet and net definitions.
All affinoid algebras here are `PresentedAffinoidAlgebra K`: actual closed
ideal quotients of a finite-variable weighted Tate algebra with arbitrary
positive polyradius. Their quotient norm and bounded algebra maps come
from `GeneralizedAffinoid.Definitions`; their completeness over complete
coefficients comes from `GeneralizedAffinoid.Banach`.

## Indexed atlas data

`Langlands.Analytic.IndexedAffinoidAtlas K X` is an indexed presentation
of the cited atlas data. The field `K` is a complete ultrametric normed
field. The ambient topological space, coefficient field and index type
have independent universes.

For each index `i` the record supplies an actual presented affinoid
algebra and an embedding
`chart i : BanachSpectrum (algebra i) → X`. Its image is the chart domain;
the embedding induces a homeomorphism from the spectrum to that domain
with the subspace topology. This is the inverse orientation of the
homeomorphism used in the original definition.

`chartDomain_injective` makes the indices bijective onto the actual
family of chart images. Thus no distinct indices carry competing algebra
data for the same member of the net. `locallyHausdorff` asserts that each
point has a Hausdorff neighborhood, and `isNet_chartFamily` uses the
published `AtlasTopology.IsNet`. Compactness and Hausdorffness of each
member follow from the spectrum embedding and are proved in
`IndexedAffinoidAtlas.isCompactFamily_chartFamily`.

For a containment of chart images, `restriction i j h` is an actual
bounded algebra homomorphism from the larger chart's algebra to the
smaller chart's algebra. `restriction_chart` identifies its spectrum
map with the inclusion in `X`. `restriction_universal` requires that
every bounded homomorphism from the larger algebra to any
`PresentedAffinoidAlgebra K` whose spectrum image lies in the smaller
domain factor uniquely through that restriction. In algebra notation
the factorization equation is `ψ.comp (restriction i j h) = φ`.
The quantifier includes arbitrary positive polyradii, hence includes
nonstrict test affinoids.

`IndexedAffinoidAtlas.range_restriction` proves that the image of the
restriction's spectrum map is exactly the inverse image of the smaller
domain under the larger chart. The forward implication is
`restriction_chart`; the reverse implication uses injectivity of the
larger chart. `isClosed_relativeDomain` then proves that this relative
domain is closed, using compactness of the smaller spectrum and
Hausdorffness of the larger one. These are the image and closedness
parts of the cited domain definition.

`restriction_id` and `restriction_comp` retain actual algebra identities
as explicit fields. The concrete construction below proves both.
Agreement of spectral point maps alone is not used to identify algebra
maps, which would be insufficient for nonreduced algebras.

## Constructed disjoint atlas

In `Langlands.Analytic.DisjointAffinoidAtlas`, let
`A : I → PresentedAffinoidAlgebra K`. `Space A` is the dependent sum
`(i : I) × BanachSpectrum (A i)` with its actual topological sum topology.
The family and the spectra may be empty. The construction imposes no
nonemptiness hypothesis.

`ChartIndex A` consists of those `i` for which `BanachSpectrum (A i)`
is nonempty. The algebra of such a chart is exactly `A i`, and its chart
map is the component inclusion. `chartDomain` is that inclusion's range;
`chartFamily` is the set of these domains. Removing empty components
ensures injective indexing and makes containment of component domains
force equality of indices.

The construction proves the following obligations.

1. `isOpenEmbedding_chart` uses the topological sum's component
   embedding. `isClopen_chartDomain` shows each range is open and closed,
   and `chartHomeomorph` identifies the actual spectrum and subspace.
   `chartDomain_eq_fiber` describes the range by the first coordinate.
2. `chart_eq_of_mem_inter` shows that meeting component domains have
   equal chart indices. To prove `chart_eq_of_subset`, choose a point
   in the smaller component using its defining nonemptiness property.
   Its image lies in both domains, so the previous equality applies.
   This proves `chartDomain_injective`.
3. `chartFamily_covers` assigns each point of the sum to its own
   nonempty component. A single open component supplies the finite
   neighborhood family required for `isQuasinet_chartFamily`.
4. `isNet_chartFamily` checks the quasinet condition on every pairwise
   intersection. If such an intersection has a point, the two indices
   are equal. Its own component then supplies the whole subspace as a
   member of the restricted family. Empty intersections have no point
   to check.
5. `isCompactFamily_chartFamily` obtains compactness from the compact
   spectrum by the continuous component map. The topological sum is
   Hausdorff because all spectrum components are Hausdorff; its
   subspaces are therefore Hausdorff. The `LocallyCompactSpace`
   instance follows from the constructed compact quasinet.
6. `restriction` first proves equality of indices from chart
   containment, then transports the bounded identity of the actual
   component algebra. `restriction_chart` follows by this equality
   and the definition of spectrum comap.
7. `restriction_universal` proves unique factorization for every
   normed commutative `K`-algebra `R` in an independent universe.
   After identifying the two component indices, the restriction is
   the identity. The factor is `φ` itself; uniqueness is equality of
   bounded algebra homomorphisms, proved pointwise on algebra
   elements. The proof needs no condition on the spectrum image,
   since contained nonempty components are equal.
8. `restriction_self` and `restriction_comp` prove the identity and
   composition algebra laws by the same component equalities and
   bounded-homomorphism extensionality.

`DisjointAffinoidAtlas.atlas` assembles these constructions into
`IndexedAffinoidAtlas K (Space A)`. The whole sum is Hausdorff, so its
universal neighborhood supplies the required local Hausdorffness.
The factorization theorem in item 7 specializes to every presented
affinoid test algebra and proves the record's full test condition.
Thus all the atlas obligations are proved from the given quotient
algebras; none are assumed of the output space.

## Scope

This module supplies a concrete family of affinoid atlases, including
the empty space and disjoint unions of nonstrict affinoid spectra.
Its chart containments are component equalities. It does not establish
the full domain universal property for a proper rational subdomain.
It also does not construct general atlas refinements, gluing, the
strong-morphism category or its localization, a structure sheaf,
étale or equivariant sites, or Harris's local tower. Those remain
separate construction obligations of the host task.
