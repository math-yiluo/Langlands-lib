# Reduction to openness at geometrically reduced Noetherian fibres

This internal supporting unit defines
`SectionComponent.NoetherianFiberwiseOpennessStatement`. For a flat, locally
finitely presented, quasi-compact and quasi-separated morphism over the spectrum
of a Noetherian ring, with an actual section, it asks that every point in the
selected component union be an interior point whenever the residue fibre at
its image is geometrically reduced. Other fibres need not be geometrically
reduced.

The statement is not proved in this unit. The theorem
`flatFinitePresentationOpenness_of_noetherianFiberwise` proves that it implies
the published arbitrary-base
`SectionComponent.FlatFinitePresentationOpennessStatement`, in every universe.

The supporting geometric-reducedness descent argument adapts the common-field
construction of the published Anthropic FLT geometric-connectedness descent
proof, specifically
`GeometricallyConnectedDescentAux.geometricallyConnected_of_pullback_snd` in
`S_AlgebraicGeometry_GeometricallyConnected_descendsAlong_surjective`.
Given any field-valued test point of the original base, surjectivity of
the base change provides a point of its pullback and therefore a common residue
field. The further base change is reduced by the geometric reducedness
hypothesis. Its projection onto the original test scheme is a base change of
a field-extension morphism, hence flat and surjective. Reducedness descends by
the published `GeometricallyReducedOfAlgClosedProof.isReduced_of_flat_of_surjective`.
An isomorphism with the canonical pullback gives the same conclusion for any
Cartesian square. Applying this result to the actual Cartesian square of
residue fibres shows that geometric reducedness of an indexed new fibre
descends to its corresponding old fibre.

The adapted FLT source is retained at commit
`6e837e75355538c7f80bab5b956861e86c4eacc2`; its Apache 2.0 attribution is
recorded in `licenses/Anthropic-FLT/LICENSE`, `NOTICE`, and `ATTRIBUTION.md`.
The changes replace the connected-space conclusion by flat surjective
descent of reducedness and package the result in the geometric-reducedness
class. The approximation and interior-neighbourhood argument are internal
constructions from the imported Library results.

For the conditional openness proof, the published locality theorem reduces
to an arbitrary affine base. `NoetherianSectionModel` supplies an actual
Noetherian model with its section and Cartesian comparison. The base-change
component equality identifies the original component union with the inverse
image of the model union. At each point of this inverse image, geometric
reducedness of its original residue fibre descends to the corresponding model
fibre. The local Noetherian hypothesis then supplies an interior point in
the model union. Continuity of the comparison map pulls that interior
neighbourhood back to the original component union.

No assertion of geometric reducedness on all model fibres or descent of that
global property to a finite stage is made. The main task still requires a
proof of the Noetherian fibrewise assertion.
