# Compact full domains and finite-cover topological descent

Worker 56 derives the topology of supplied full affinoid domains and their
finite covers from the actual bounded spectra. The declarations belong to
`Langlands.Analytic.PresentedAffinoidAlgebra.Domain`.

## Inputs and provenance

The field `K : Type u` is a complete ultrametric normed field. Its valuation
may be trivial. The fixed base `A : PresentedAffinoidAlgebra K` and each
domain's representing algebra are actual finite positive-polyradius closed
Tate quotients, with their published quotient norms. A full `Domain K A`
contains a bounded structural algebra map, a closed subset of the base's
bounded multiplicative spectrum, an exact image equality and the universal
factorization property against every presented positive-radius affinoid
test. These are the published objects, not new abstract analytic spaces.

The registered original is V. G. Berkovich, *Non-archimedean analytic
spaces* (Trieste lectures, 2009), source ID
`berkovich-2009-trieste-analytic-spaces`, PDF SHA256
`8cfe4f6f35d5e717ac67c5c8f5ef9ff9185f460bbe5f9a10aeacd84cddeeb2ca`.
Definition 1.2.5 on printed/PDF p.4 gives the evaluation topology and
Fact 1.2.6 gives spectrum compactness for a nonzero Banach ring.
Definition 2.2.1 on p.9 supplies the closed subset, exact image and full
affinoid-test property used in the imported domain definition.

The present results are internal topological consequences of these inputs;
the source does not separately name the quotient-map descent construction.
The imported `Spectrum.Properties` proves compactness and the Hausdorff
property by realizing the spectrum as a closed subspace of the product of
the intervals `[0, ‖a‖]`. Its compactness proof also covers a zero ring,
whose spectrum is empty. All uses of spectrum compactness here reuse that
proved result, including in the empty case.

## A single domain

`isCompact_locus` applies closed-subset compactness in the base spectrum.
`compactSpace_locus` equips the locus subtype with the resulting
`CompactSpace` instance. Its Hausdorff property is inherited from the
base spectrum.

The already constructed `spectrumToLocus` is a continuous surjection from
the actual representing quotient spectrum to the represented locus.
`spectrumToLocus_isClosedMap` uses compactness of its source and the
Hausdorff property of its target. Together with surjectivity this proves
`spectrumToLocus_isQuotientMap`. The three ensuing equivalences detect
openness, closedness and continuity after pullback along this structural
map. The continuity target is any topological space `Y : Type v`; no
separation condition is imposed on `Y`.

`Inclusion.locusMap_isClosedEmbedding` proves that each actual domain arrow
induces a closed embedding on loci. Its locus map is continuous and
injective because it preserves the underlying base point, and the source
locus is compact and the target Hausdorff. The representing-spectrum map
is not asserted to be injective.

## Actual finite covers

`FiniteCover V` consists of a natural number `size`, domains
`obj : Fin size → Domain K A`, actual domain arrows `map i : obj i ⟶ V`,
and the requirement that every point of `V.locus` lies in some component
locus. Each arrow stores its bounded algebra restriction in the opposite
direction and the equation over `A`. Thus the cover data includes the
existing actual analytic maps, not just inclusions of arbitrary subsets.

`singleton V` uses the identity restriction and constructs a one-member
cover. `empty V hV` constructs a zero-member cover when
`hV : V.locus = ∅`. Conversely, `locus_eq_empty_of_size_eq_zero` shows
that any zero-member cover has empty target locus. Neither a nonempty
target nor a positive cover size is assumed in the general results.

For a cover `c`, `componentMap c i` is the continuous map from
`BanachSpectrum (c.obj i).algebra` through its own locus and then along
`(c.map i).locusMap` into `V.locus`. The published naturality equation
for an actual domain arrow identifies this map with restriction on
spectra followed by the target's structural spectrum-to-locus map.
`componentMap_isClosedMap` follows from compactness and Hausdorffness.

`totalMap c` assembles the component maps on the topological disjoint
union

`Σ i : Fin c.size, BanachSpectrum (c.obj i).algebra`.

The coproduct topology makes this assembled map continuous.
`totalMap_surjective` chooses a component containing a given target point
and then a point of its representing spectrum using that domain's exact
structural image. The index type is finite, so Mathlib's finite disjoint
union compactness instance makes the source compact.
`totalMap_isClosedMap` and `totalMap_isQuotientMap` now follow as for a
single domain.

## Descent equivalences and scope

For every subset `s` of `V.locus`, `FiniteCover.isOpen_iff` and
`FiniteCover.isClosed_iff` state that `s` is open or closed exactly when
its preimage in every component's actual representing spectrum has that
property. `FiniteCover.continuous_iff` says that a given function
`g : V.locus → Y` is continuous exactly when every composite with a
component spectrum map is continuous. The proofs combine the quotient
topology of `totalMap` with the componentwise descriptions of open sets,
closed sets and continuous maps on a topological disjoint union.

The three `_loci` variants replace component spectra by component loci.
They follow by applying each component's proved structural quotient-map
equivalence. These results include the zero-member cover: all component
conditions are vacuous and its target locus is empty.

This unit constructs topological descent for finite covers of supplied
full domains. It provides no new rational-domain representations, domain
intersections, generic injectivity of `spectrumToLocus`, analytic atlas,
structure sheaf, étale site or cohomology construction. In particular,
the openness criterion concerns preimages of a target subset; it does
not assert that the cover's domain inclusions are open maps.
