# Parabolic intersections with a reductive factor of a central product

Worker 715.

This internal construction supplies the field-level parabolic intersection
argument used in the derived-group correspondence. It is derived from the
published central-isogeny power lift, bounded exponent of the actual kernel,
positive-power invariance of dynamic parabolics, closed-subgroup reflection
of orbit extensions, and the parabolic-dynamic characterization. It does not
prove the correspondence over a general base.

For any base scheme, a cocharacter of `Z × D` followed by multiplication into
`G` induces exactly the same conjugation orbit as its `D` coordinate, provided
`z : Z → G` is central. Consequently their dynamic parabolic subgroup functors
agree on every test scheme. No property of `z` other than centrality is used
in these two lemmas.

Now let `k` be any field, `G` a connected reductive group over `k`, and
`d : D → G` a closed embedding. Suppose `z : Z → G` is central and the
multiplication map `Z × D → G` is a central isogeny. For every parabolic
`i : P → G`, `exists_intersection_cocharacter` constructs a cocharacter
of `D` whose dynamic parabolic is exactly the range of the first projection
`D ×_G P → D`. This part does not require reductivity of `D`.
`intersectionCocharacter` chooses such a cocharacter, and
`range_intersectionCocharacter` proves its all-test range identity.

The proof chooses a cocharacter of `G` presenting `P`. A positive integer
kills every point of the scheme-theoretic kernel of the central isogeny.
The power-lift theorem therefore lifts a positive power of the cocharacter
to `Z × D`. Projection to `D`, removal of the central coordinate from
conjugation, and invariance under positive powers identify the ambient
dynamic parabolic. Reflection through the closed embedding `d` then
identifies its inverse image with the dynamic parabolic in `D`.

If `D` is also connected reductive, `isParabolicSubgroup_intersection`
applies the published parabolic-dynamic recognition theorem to this closed
intersection. It proves that the actual intersection projection is a
parabolic subgroup, including smoothness; smoothness is not an additional
premise.

The field may be imperfect or have positive characteristic. All declarations
are universe-polymorphic. The result assumes the global central product
isogeny; it neither constructs that isogeny nor supplies relative smoothness,
relative central-factor containment, or the inverse parabolic construction
over an arbitrary base.
