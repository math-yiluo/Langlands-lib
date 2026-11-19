# Finite generating sections for a fixed coefficient level

This module derives uniformity at a fixed input level for the wave-packet
argument of Waldspurger VI.3.1, printed pp. 302–305. It uses the actual
compact restriction, self-twist action and fixed coefficient space.
[Waldspurger (2003)](https://doi.org/10.1017/S1474748003000082)

`HasOrbitSectionLevelFiberGenerators` says that one finite collection of
sections at level `H` realizes each vector of a displayed coefficient
basis at every unitary torus parameter. The realizing section may depend
on the vector and the parameter. The proof requires `H ≤ K`, a finite
basis and a finite unitary class stabilizer.

The stabilizer action preserves the fixed coefficient subspace by its
commutation with the original compact product action. At each parameter
the proof chooses a smooth Lagrange scalar on its finite stabilizer orbit.
A smooth transition applied to the real part makes the scalar equal to
one in a neighborhood of the chosen parameter and zero near the other
points of the orbit. Averaging its translates against the stabilizer
action gives an equivariant family equal to any prescribed vector on
one open neighborhood. This neighborhood works for every vector of the
fixed space.

The original compact restriction and orbit family equivalences lift
these families to smooth sections. Because each compact value belongs
to the same fixed space, the lifted sections are at level `H`.
Compactness of the unitary torus gives a finite subcover. Taking the
lifted sections for the finitely many chosen neighborhoods and basis
vectors proves the generator property.

`exists_uniform_fiber_zero_threshold` applies to any fiberwise linear
expression whose vanishing region shrinks as the threshold increases.
If the expression vanishes beyond some positive threshold for each
section, one threshold works for the whole fixed space. The proof takes
a common threshold for the test sections and uses the resulting vanishing
on each basis vector to conclude linear-map equality.

`exists_uniform_fiber_basis_exponential_bound` applies to a fiberwise
linear expression with a nonnegative weight and a nonnegative real
quantity in the exponential. Per-section bounds give one positive
exponential rate and a nonnegative multiplier that work for all basis
vectors and all unitary parameters. The rate is the minimum of one and
the finitely many test-section rates, and the multiplier is the sum of
their multipliers. The two estimate lemmas take the linear expressions
and their per-section estimates as inputs.
