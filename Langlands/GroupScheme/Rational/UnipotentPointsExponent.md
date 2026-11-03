# Uniform power exponents for unipotent groups in positive characteristic

This derived development proves an exponent bound on the actual groups of
points over every relative scheme test, at arbitrary universe `u`.
`HasUniformPowerExponent G q` means that every such point has q-th power one.
A monic subgroup inherits this predicate by cancellation; no independent
unipotence assertion for the subgroup is needed.

For a unit x in any associative ring receiving a homomorphism from a field of
prime characteristic p, if `(x-1)^m=0` and `m ≤ p^r`, then `x^(p^r)=1`.
The proof handles the trivial target ring directly. Otherwise the field map
is injective and transfers characteristic p. The binomial identity for the
two commuting elements x and 1 gives
`(x-1)^(p^r)=x^(p^r)-1`; the higher power of the difference vanishes by the
bound. No commutativity of the whole ring is assumed.

Applied to the matrix ring over the global sections of an arbitrary test,
the proved `UnipotentProductBound` power corollary supplies the nilpotent
difference. The scalar matrix map composed with the base-field scalar map
is the required field homomorphism. The argument includes zero-dimensional
matrix rings and empty tests, where the relevant ring can be trivial.
A faithful actual representation then transfers the bound back to the
point group.

An affine locally finite type unipotent group scheme over any field of prime
characteristic p has a single faithful finite-dimensional representation.
If its dimension is m, choosing r=m gives `m ≤ p^m`. Thus the final theorem
gives a single p-power exponent before quantifying over any test scheme.
It assumes neither smoothness nor connectedness nor algebraic closedness.

The provenance is the explicit binomial argument using the earlier uniform
matrix-difference power theorem and the published affine linear embedding.
This result does not produce a smooth p-torsion subgroup, vector coordinates
or equivariant linearity, and does not complete the ordered-product theorem.
