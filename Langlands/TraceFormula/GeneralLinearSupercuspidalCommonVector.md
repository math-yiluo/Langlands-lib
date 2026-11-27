# A common cuspidal vector for prescribed local supercuspidals

Choose at every prescribed finite place a vector and a smooth dual covector
with pairing one. Form the compact adelic tensor of their inverse coefficients,
a nonnegative archimedean bump positive at the identity, and the characteristic
function of the integral subgroup away from the prescribed places. After positive
averaging, the support is contained in a compact set on the norm-one group.
A further cutoff at the supplied auxiliary place removes every nonidentity
rational point of that compact set. The resulting periodization has a nonzero
identity value because all its finite factors equal one on the positive subgroup.

The conjugate periodization then detects a nonzero quotient convolution. At any
one of the prescribed places, all two-sided slices are scalar multiples of
translated local coefficients. Their radical integrals vanish, so the adelic
radical comparison and `groupSchemeCuspidalImage` put the convolution in the
actual almost-everywhere cuspidal Hilbert space.

Varying one local vector while holding the other factors fixed makes the test
linear in that vector. Convolution against the same input produces an
intertwiner for the determinant-unit subgroup, by left translation of the
weight. Each of these maps sends the chosen local vector to the same nonzero
cuspidal vector. The away integral factors and auxiliary cutoff make this
vector fixed at each finite place outside the prescribed and auxiliary places.

The cuspidal-image step uses the vanishing condition in Getz–Hahn,
*An Introduction to Automorphic Representations* (2024), Definition 16.4.1
and Lemma 16.4.2, printed p. 430. The identity-term isolation and simultaneous
local intertwiners follow from the compact tensors and this convolution argument.
