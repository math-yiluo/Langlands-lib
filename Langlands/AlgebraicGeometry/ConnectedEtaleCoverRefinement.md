# Connected refinements of étale covers over local spectra

Worker 635.

This is an internal consequence of the topology of a local spectrum,
openness of étale morphisms, and the published openness of connected
components of locally Noetherian schemes.

`surjective_of_isOpenMap_of_closedPoint_mem` observes that every point
of a local spectrum specializes to its closed point. An open image
containing that closed point therefore contains every point.

`connectedComponentOpen_surjective_of_closedPoint` applies this fact to
the actual open connected component through a point above the closed
point. The composite remains open, and its image still contains the
closed point. Its hypotheses allow any open morphism from a locally
Noetherian scheme to a local spectrum.

`exists_connected_etale_refinement` starts with an étale surjection to
the spectrum of a Noetherian local ring. Local finite type over the
Noetherian base makes the source locally Noetherian. Surjectivity
supplies a point above the closed point, and its open connected
component is connected, étale over the base, and still surjective.
No domain, valuation, Henselian, residue-field or quasi-compactness
hypothesis is used. This lemma supplies only a refinement of a given
cover, not the existence of a trivializing cover for any outer scheme.

`connectedEtaleRefinementOpen` chooses the resulting open subscheme.
Its connectedness, étaleness over the base and surjectivity are exposed
as instances, so consumers can use the actual restricted cover.
