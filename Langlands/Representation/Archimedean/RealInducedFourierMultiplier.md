# Induced Fourier coefficient weights

`InductionStages.RealInducedFourierMultiplierStatement` starts with a
linear middle operator whose compact iterated Fourier coefficients
are fixed multiples of the input coefficients. Its induced map has
the same coefficients and multipliers in the embedded middle
coordinates.

The proof identifies an iterated ambient coefficient at a compact
element with the corresponding coefficient of the normalized middle
slice at the identity. A shift of a rotation slot inserts the local
rotation into the same two coordinates in the full group. The
normalizing slice factor is one along these compact rotations.
The Library's slice formula for the induced operator then reduces
the claim to the local coefficient identity.

`iteratedFourierMultiplier_comp_of_disjoint` assembles the coefficient
weights for two such operators on disjoint sets of coordinates. It
splits the mode list between the two slot lists. The Fourier
integrations for disjoint rotations commute, so the two multipliers
contribute the product of their weights.

This is an internal consequence of the Library's block rotations and
normalized induction in stages. It permits local forward replacement
multipliers to retain their weights in a grouped standard module.
