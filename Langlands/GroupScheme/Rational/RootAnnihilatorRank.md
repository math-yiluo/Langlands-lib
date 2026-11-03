# Codimension of independent-character annihilators

Author: Worker 1322.

This derived linear-algebra unit concerns the existing character lattice and real
cocharacter space of an actual split torus over an arbitrary field. It introduces
`RealTorusSpace.rootEvaluation T J`, whose coordinates are the existing character
evaluations, and identifies its kernel with the published `rootAnnihilator T J`.

For a finite selection `J` whose images in the rationalized character lattice are
linearly independent, `rootEvaluation_surjective` proves that every real coordinate
vector occurs. The proof uses the published
`IsSplitTorus.exists_scaled_pairings`: for each coordinate it obtains an integral
cocharacter with a positive integer multiple of the corresponding coordinate
vector as its pairings. Tensoring these cocharacters with the prescribed real
coordinates divided by those positive integers, and summing, supplies an explicit
preimage.

If the ambient real cocharacter space is finite dimensional,
`finrank_rootAnnihilator_add_card` applies rank-nullity to this surjective map.
It gives the dimension of the annihilator plus `Nat.card J` equal to the dimension
of the full real cocharacter space. The proof retains an empty selection and
rank zero, and asserts no equality of integral lattices.

The provenance is internal and derived from the existing scaled-pairing theorem
and finite-dimensional rank-nullity. No external source is invoked. Independence,
finiteness of `J`, and finite dimensionality of the ambient space are explicit
intermediate hypotheses. This unit does not prove the unrestricted
`StandardLeviCentralDirectionsStatement`, intrinsic independence of simple roots,
or the geometric realization by the split component of a standard Levi.
