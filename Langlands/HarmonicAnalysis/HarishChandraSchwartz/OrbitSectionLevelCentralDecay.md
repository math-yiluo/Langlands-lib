# Central Fourier decay uniform over a fixed section level

This module is an internal finite-level strengthening of the published
`OrbitWavePacketDecay.exists_norm_inducedOrbitWavePacket_le_xi_rpow` argument.
It combines that argument with `OrbitSectionFixedTensor` and
`TorusMonomialSeminormControl`. All declarations are in
`Langlands.HarishChandraSchwartz`.
The coefficient transport identity is reused from
`OrbitSectionLevelCoefficientBound`.

The setting is the existing general topological group, semidirect parabolic
and Levi, compact open subgroup `K`, irreducible admissible complex Levi
representation, square-integrability modulo the given central subgroup, actual
unitary-twist orbit and its finite self-twist stabilizer. Group, representation
carrier, character indices and torus coordinates retain independent universes.
The character measure `ρ` is arbitrary finite and left invariant. The weight
`w` pulls back to a smooth function on the coordinate torus. Laurent unitary
coordinates and continuity of the coordinate equivalence are explicit premises.
The lattice homomorphism `nG : G →* Multiplicative (L → ℤ)` is trivial on `K`
and `U`, and its character restriction to `M` agrees with the integer monomial
map `a : J → L → ℤ` in the given coordinates. These are the same analytic and
character compatibility premises as in the existing central decay theorem.

`exists_levelOrbitWavePacket_central_decay_of_coefficient_bound` accepts an
ambient function `Xi` and a bound for the twisted coefficient of each fixed
compact-picture vector by a positive constant times `Xi`. The constant is
uniform over the unitary coordinate torus and the group. This interface lets
the standard-Levi application use the projection of the parabolic intersection
of `K` as its inducing compact subgroup.

`exists_levelOrbitWavePacket_central_decay` specializes this estimate to the
original Iwasawa function `xi hP₀K δ₀`. It obtains the fixed-vector bound from
`norm_twist_coefficientMap_le_xi`, using the unimodular unipotent modulus,
Levi/Iwasawa data, compact triviality of the minimal-parabolic modulus, and
lower Levi coefficient bound. Both theorems use `CompactOpenCofinal M` to
obtain finite dimensionality of the actual fixed coefficient space.

For any open subgroup `H ≤ K` and real `r`,
each theorem chooses a finite set `t` of the
existing input derivative/ambient-dual indices and a nonnegative constant `c`
**before** the varying section `q`. For every `q` at exactly that input subgroup
and every `g`, it bounds the norm of the literal `inducedOrbitWavePacket` by

`c * (t.sup (OrbitSectionLevel.seminormFamily ... H)) q * Xi(g)
   * (1 + norm (toAdd (nG g)))^(-r)`.

The conclusion is uniform in all sections of the fixed input level and all
group points.

The proof chooses a finite basis of `orbitSectionFixedCoefficients ... H` using
the published admissibility and fixed-vector finiteness theorem. It extends its
basis coordinates algebraically to linear functionals on the ambient compact
picture. The scalar functions obtained by applying those functionals to the
actual section restriction are smooth. The fixed-valued restriction and the
basis expansion identify their sum with the original restriction at every torus
point. The coefficient transport identity then gives an exact finite expansion
of the actual orbit coefficient in these functions and the twisted coefficients
of the fixed basis vectors.

`exists_levelCoordinate_derivative_control` collects all ordered derivative
lists through a prescribed order and all finitely many ambient coordinates into
one finite set of original input seminorm indices. Definitional agreement of
the scalar and section derivative seminorms bounds each coordinate's
`smoothTorusDerivativeControl` by this finite supremum. No extension of
continuous linear functionals or change of topology is used.

The fixed-vector input bounds the twisted coefficient of each basis vector
uniformly on the unitary torus. Laurent coordinates give continuity in the
character, and the character compatibility conditions give equivariance under
the auxiliary central torus. For `k = Nat.ceil r`, the scalar weighted
monomial estimate bounds the product of the weight and each scalar
coefficient, and its `k`th pure derivatives along that torus, by `A` times the
finite input supremum, with a single `A ≥ 0` independent of the section and
basis coordinate.
The published Fourier averaging estimate applies to each summand; its integrals
are integrable by continuity on the compact torus. Triangle inequalities and
finite sums give the stated result. The auxiliary Haar probability measure
occurs only in this averaging proof.

The coefficient basis, constants and derivative indices are all chosen before
`q`. More explicitly, the scalar multiplier can be chosen as
`S⁻¹ * sum i, 2^k * (1 + card L) * A * (ρ.map e).real univ * B i`, where `S`
is the finite stabilizer cardinality and `B i` are the basis-vector Xi bounds.
Thus the packet keeps the original stabilizer divisor and character-measure
mass.

`orbitSectionLevelCentralControl H hHK r` chooses such `t` and `c` and forms
the seminorm `c • t.sup inputSeminorms` on the existing section level.
`norm_levelOrbitWavePacket_le_centralControl` gives the same bound with this
seminorm as the entire input factor.
`continuous_orbitSectionLevelCentralControl` proves its continuity from the
existing `OrbitSectionLevel.withSeminorms`, continuity of finite suprema and
nonnegative scalar multiplication.

The output decay concerns the lattice `nG`. To deduce a full-height estimate
on a region, a caller can supply a height comparison with `nG` there.
