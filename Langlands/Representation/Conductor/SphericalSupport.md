# General-field smooth root support

This internal prerequisite proves uniform root bounds for actual smooth
Whittaker coefficients over every nonarchimedean local field. The field universe
`uF` and representation-space universe `uV` are independent. The representation
need not be irreducible or admissible, and its Whittaker functional may be zero.
The conclusions do not assert degree compactness, convergence, essential-vector
existence or a conductor theorem.

Write `v_F` for `ValuativeRel.valuation F`, `O` for its integer subring, and
`ϖ : Fˣ` for a uniformizer. The data-valued definition
`uniformizerPowerLattice ϖ m` is the closed ball
`{x : F | v_F(x) ≤ v_F(ϖ)^m}` for an integer `m`. The lemma
`uniformizerPowerLattice_mul_integer` puts `ϖ^m y` in this ball for every
`y ∈ O`, using multiplicativity of the valuation and `v_F(y) ≤ 1`.

`exists_uniformizerPowerLattice_subset` proves that these balls are cofinal in
the neighborhoods of zero. A neighborhood contains an open valuation ball of
nonzero radius. Surjectivity of the canonical valuation and the defining
uniformizer property express this radius as `v_F(ϖ)^m`. Since
`0 < v_F(ϖ) < 1`, the closed ball of exponent `m + 1` lies in that open ball.
This proof uses the general valuative topology, without a characteristic-zero
or p-adic-field restriction.

For a smooth representation `π` of `GL_(r+1)(F)` and a vector `v`,
`exists_uniformizerPowerLattice_fix_integral_orbit` produces one integer `m`
such that

`π(1 + t E_(i,i+1)) (π(κ) v) = π(κ) v`

for every adjacent index `i : Fin r`, every `κ ∈ GL_(r+1)(O)` and every `t`
in this ball. Smoothness makes the orbit map locally constant. Compactness of
the actual level-zero integral subgroup makes its vector orbit finite.
For each of its finitely many vectors and the finitely many adjacent roots,
the inverse image of that vector is an open neighborhood of zero. The finite
intersection is open, and the preceding cofinality result supplies a common
uniformizer ball. Continuity of the root map is proved directly for the
published `UpperUnipotentCharacter.adjacentUnit` matrices and their inverses.

`model_diagonal_root_integral_bound` applies this common bound to an actual
vector `f` in the coefficient model of a Whittaker functional `ℓ` for a
unitary additive character `ψ` with `HasIntegerConductor ψ`. It gives one
integer `m` such that, whenever

`f(diagonalUnits a * κ) ≠ 0`, with `a : Fin (r+1) → Fˣ` and
`κ ∈ GL_(r+1)(O)`,

each `((a i.castSucc / a i.succ : Fˣ) : F) * ϖ^m` belongs to `O`.
Surjectivity of the actual model map first represents `f` by a vector `v`.
Conjugating an adjacent root through the diagonal multiplies its parameter by
`a_i/a_(i+1)`; the proof verifies this identity entry by entry. The standard
Whittaker character on that root is exactly `ψ` of its parameter, as follows
from the first-superdiagonal sum. Applying `ℓ` to the fixed-vector identity and
cancelling the nonzero coefficient shows
`ψ((a_i/a_(i+1)) t) = 1` throughout the common ball. Taking `t = ϖ^m y`
for every `y ∈ O` and using the second clause of `HasIntegerConductor` gives
the claimed integrality.

The provenance is internal: these are direct deductions from the published
uniformizer, local-field topology, smooth orbit, compact congruence-subgroup
and coefficient-model definitions, together with elementary matrix identities.
They supply a general-field support ingredient for the degree-integral method;
neither the desired integral identity nor any essential-vector conclusion is
introduced as a premise.
