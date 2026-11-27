# Actual continued standard pairs through a represented intermediate Levi

`realizedContinuedPair_square` relates an actual `ContinuedPair` in the
ambient group to a full-domain continuation of the actual lower pair.
The lower presentation is pulled back with `continuationRestrict` along
the specified morphism of parameter schemes. Surjectivity of the source
restriction and `realizedNested_domain_eq_top` give full convergence of
the lower family at the ambient convergence parameters. The two twists
and their compact charts use the prescribed inducing equivalence.
`HasIntegral.map_induced` identifies the represented weak integral in
the transported lower chart. Then `realizedContinuedIntertwining_square`
gives the equality of the two continued maps with the quotient-measure
scale.

`exists_realizedContinuedRoundTrip_scalar_scale` uses the two directions
of the square and a lower nonzero vector with an ambient lift. This
compares the scalar of the ambient composite to the lower scalar with
the product of the two measure scales.
