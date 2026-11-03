# Smooth generation by a geometrically reduced affine source

`GeometricallyReducedAffineImageGenerationStatement` specializes Milne,
*Algebraic Groups* (2017), Proposition 2.50, printed pp.55–56 (PDF pp.71–72),
to affine sources and affine ambient groups. The affine construction and its
preservation of geometric reducedness appear in Propositions 2.46–2.48,
printed pp.54–55 (PDF pp.70–71). The registered source is
`milne-2017-algebraic-groups`, SHA256
`899b0f44f3c3ccfbaf5ed1cf9c180be7a8016b1c0e9709ca0c206304e5bd1cd0`.
The retained official errata snapshot, source
`milne-2017-algebraic-groups-errata-2026-11-02`, has no correction to these
propositions in its Chapter 2 entries.

Over an arbitrary field in an arbitrary universe, let `G` be an actual affine
group scheme locally of finite type, and let `V` be an affine scheme locally of
finite type and geometrically reduced over that field. For every actual
morphism `f : V ⟶ G.X`, the statement asks for a `GeneratedImage f` whose group
scheme is smooth over the original field. Affineness makes the two locally
finite type hypotheses finite type.

The existing `GeneratedImage` data include an actual closed subgroup inclusion
and equality of its represented subgroup functor with `closedImageEnvelope f`.
That envelope is the intersection of all actual closed subgroup functors
through which `f` factors. Thus the requested subgroup is minimal on all test
schemes, including nonreduced and nonaffine tests. The factor morphism and the
minimal homomorphisms into competing closed subgroups are already consequences
of this data in `ImageGeneration`.

There is no connectedness or geometric integrality assumption, no chosen point
of `V`, and no smoothness assumption on `G`. Empty sources are allowed. The
statement asserts no dominance of an individual finite product: even a finite
set of points can generate a positive-dimensional torus. Closedness of the
inclusion also implies that the representing group is affine and locally of
finite type, but these consequences are not additional output fields here.

This is a proposition definition recording a proof obligation. It supplies no
proof of geometric generation or of derived-subgroup smoothness.
