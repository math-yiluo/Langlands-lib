# Affine finite type first levels of affine étale charts

This internal construction supplies the final chart restriction in the proof
route for Stacks Proposition 70.8.1, Tag 07SU, from the registered source
`stacks-noetherian-approximation-2026-11-01`. The finite symmetric tuple charts
come from Tag 0BBN in `stacks-stratification-2026-11-02`. The new results are
derived from the imported, proved stable-level, étale-object descent and
chart-comparison interfaces. They do not assert the unconditional first-level
theorem.

`AffineFiniteTypeFirstLevel.nonempty_chart` starts with an affine object
scheme and an actual affine finite type first level of its relation. For
any affine scheme with an étale map to that object scheme, it constructs a
first level of the induced relation on the chart. No invariance of the
chart is assumed. The existing affine étale-object descent theorem descends
the chart to a stable finite level, with its actual pullback square.
The chart-comparison theorem gives a cartesian morphism of induced relations.
The descended chart is affine and étale over the finite type stable object,
so it is locally of finite type over the absolute terminal scheme. Its arrow
scheme is affine as an iterated pullback of affine schemes.

`AffineFiniteTypeFirstLevel.chart` chooses one of the first levels supplied
by `nonempty_chart`. Its output retains the actual descended relation and
cartesian comparison, together with the affine and finite type properties.

`nonempty_affineFiniteTypeFirstLevel_tupleChart_reindex` applies this
construction to an injectively selected finite tuple family. Its inclusion
is an open immersion of affine object schemes. The existing actual
arrow-scheme isomorphism identifies the selected presentation with the
induced chart relation, with identity object map. Composing the resulting
cartesian morphism with the chart's first level gives the stated result.

`nonempty_affineFiniteTypeFirstLevel_of_tupleFinite` applies chart descent
to the original object's length-zero inclusion in the finite tuple family.
The existing zero-chart arrow isomorphism gives a cartesian comparison from
the original relation to that induced chart. Composition therefore gives
a first level of the original relation.

`nonempty_affineFiniteTypeFirstLevel_of_tupleTail_zero` instead selects
the length-zero component of the tail indexed by all lengths from zero to
`N`. The selected singleton presentation is identified with the original
relation by the existing object and arrow isomorphisms. These commute with
both endpoints, and their source square is a pullback because its horizontal
maps are isomorphisms. This gives the final transfer directly from a first
level of the zero tail, without changing the tail's indexing type.
