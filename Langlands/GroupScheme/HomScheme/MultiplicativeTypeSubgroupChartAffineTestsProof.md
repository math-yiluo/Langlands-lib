# Extending multiplicative-type charts from affine tests

`MultiplicativeTypeSubgroupModuli.isOpenChartOfAffines` proves
`IsOpenChartOfAffinesStatement`: affine injectivity and affine
open-subfunctor criteria suffice for all test schemes. It constructs
no chart and imposes no hypothesis on the ambient group.

The proof reuses the published generic torus-family lemmas
`TorusSubgroupModuli.evaluate_eq_comp` and
`evaluate_eq_iff_openCover`, neither of which has a torus hypothesis.
The first restricts equality of evaluated ranges; the second detects
it on any open cover, using closed-immersion monomorphy and Zariski
locality of actual subgroup ranges.

Affine injectivity extends to all schemes by checking maps on an
affine cover. Local parameter maps then agree on overlaps and glue;
equality of their subgroup evaluations also glues. For an affine base
of the comparison family, its affine openness criterion consequently
handles arbitrary further tests. On a general comparison base, apply
this to an affine cover and take the union of the resulting open
loci. A map into this union is locally in one of the loci, so its
parameter maps glue. These constructions supply all fields of
`IsOpenChart`.

This is an internal derived proof, adapted from the published
`TorusSubgroupChartAffineTestsProof`. The only change in the source
property is from relative torus to relative multiplicative type;
the proof uses that property solely through stability under base
change, supplied by the imported multiplicative-type API.
