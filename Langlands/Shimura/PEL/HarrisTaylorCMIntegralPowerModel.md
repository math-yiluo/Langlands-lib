# An integral isogenous model for an even power of a CM self-isogeny

This internal result works at the identity geometric point of an algebraically
closed characteristic-zero field spectrum. It retains the existing prerequisites
for actual duals, polarizations, finite-etale torsion and the finite-adelic Tate
comparison. The original compact Harris level is arbitrary.

`harrisCMFrameLattice_realized` realizes the literal integral finite-adele lattice
of every compatible Harris frame by an actual abelian scheme B and a rational
isomorphism r from B to the original scheme. Its equation identifies that lattice
exactly with the image under r of the full integral Tate group of B. The proof
uses the already proved integer bounds for the frame lattice. The actual
monodromy at the identity field point is trivial. The original geometric
polarization supplies the finite-set fibre-affineness condition via its ample
diagonal bundle and the proved proper-fibre affine-neighbourhood result.
The proved commensurable invariant lattice realization theorem then applies.

`IntegralPowerModelWitness` asserts a compatible frame, a strictly positive
integer m, the multiplier equality q^(2m)=1, such an exact realizing pair B,r,
and an actual automorphism g of that same B. The rationalization of g is
r.hom followed by the 2m-th power of the original underlying rational
self-isogeny and then r.inv. The inverse has the corresponding exact equation.

`integralPowerModelWitness_of_levelIso_fixed` proves the witness from fixedness
of an orbit at an original compact Harris level. It first uses the proved
even-power lattice witness, realizes that same frame lattice as above, and
applies `realizedLatticeStabilizer` to the actual power. The monoid homomorphism
from rational automorphisms to rational endomorphisms identifies the power in
the two conventions. Both rationalization equations come from integral Tate
reflection on the specified realizing scheme.

The provenance is an internal composition of these imported, proved geometric
and Tate results. This unit constructs an integral automorphism; it does not yet
prove that g preserves a polarization, that g has finite order, or that the
original self-isogeny is the identity at sufficiently small level.
