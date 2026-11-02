# Point lifts for relative spaces

This internal construction concerns the published relative-space functor for
a morphism `f : X → S`. A map `r : V → T ×_S X` determines a test scheme
`pointBase f r` over `S`, whose underlying scheme is `V`. If `r` factors
through the relative-space map induced by `h : U → T`, the chosen factor
`a` determines a base map `pointLift f h r a` to `U`. Pullback along the
point section followed by the induced relative-space map recovers `a`.

Equal composites of the total-space lifts yield equal composites of their
base lifts. Both the base lifts and the point sections commute with
precomposition. The implementation proves these assertions from the actual
fibre-product projections, their universal properties and naturality of the
relative projection.

These are derived intermediate constructions toward module descent data.
They make no assertion of effective descent or the final fppf comparison.

The second-projection identity is reused from
[RelativeGeometry](RelativeGeometry.md) as
`Langlands.AlgebraicGeometry.Picard.relativeSpace_map_snd`.
