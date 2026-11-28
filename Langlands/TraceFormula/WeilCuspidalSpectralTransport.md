# Compactness and multiplicity one for Weil-restricted GLₙ

`weilCuspidalSpectralTransport` proves `WeilCuspidalSpectralTransportStatement`
for the full almost-everywhere cuspidal subspace of the positive rational
quotient of the adelic Weil restriction. The lower central split torus has
injective character restriction with finite-index image. The assertion uses
the given parabolic dynamics and lower norm-one Haar right invariance. Every
continuous compactly supported weight gives a compact operator on this
cuspidal space. Two closed irreducible invariant subspaces coincide if a
linear isometric equivalence intertwines their actions.

The proof uses `map_positiveImage` to identify the lower positive subgroup
with the upper scalar positive subgroup. The adelic comparison and
`cuspidalEquiv` then identify the group actions on the two actual cuspidal
spaces.

For compactness, pull the test back to the upper adelic group along the
inverse of the group comparison. The pushforward of lower adelic Haar is a
scalar multiple of upper adelic Haar by Haar uniqueness. Changing variables
in the Bochner integral expresses the lower operator as a scalar times the
conjugate of the upper operator by `cuspidalEquiv`. Compactness follows from
`generalLinearFullAEL2CuspidalCompactness` and stability of compact operators
under continuous linear composition and scalar multiplication.

For multiplicity one, the positive rational quotient Haar comparison gives
the same positive norm factor, the square root of the quotient measure
factor, on every vector under `cuspidalEquiv`. Pulling the two subspaces back
therefore preserves closedness, invariance and irreducibility. Conjugating
their intertwining isometry gives an upper intertwining isometry, since the
two norm factors cancel. `generalLinearCuspidalMultiplicityOne` identifies
the pulled-back subspaces, and surjectivity of the cuspidal equivalence gives
equality on the lower side.
