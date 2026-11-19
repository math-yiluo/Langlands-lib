# Analytic-domain embeddings from finite compact domain covers

A `FiniteCompactDomainEmbeddingCover f` consists of finitely many
compact analytic domains covering the source of `f`, together with
an analytic-domain embedding for each restriction of `f`.

Suppose the source is Hausdorff and `f` has an analytic retraction.
The retraction identifies the source topologically with the image.
The images of the cover domains are therefore compact and closed
in that image. They form a finite closed quasinet cover, and
their original chart families refine it. This gives the actual
analytic-domain structure on the image.

The map to the image domain and the restriction of the retraction
give the two arrows of the isomorphism. One composite is the
identity by the retraction equation, and the other follows by
checking both maps on the covering domains. Equality on those
domains detects equality of full localized morphisms.

This internal result can assemble local descriptions of an
analytic diagonal, whose projection is a retraction.
