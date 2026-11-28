# Continuous sections of real standard tail quotients

`RealBlockSmoothTailSectionStatement` concerns a rank-matched real standard
module with a nonzero-weight induced block at a specified position. The
source list replaces that block by its two ascending character positions,
with parities satisfying the tail condition. The statement gives continuous
complex-linear maps between the genuine smooth carriers with their word
topologies. The forward map is equivariant under the actual general linear
group and surjective, with the reverse map as a continuous linear right
inverse. On compact-finite vectors these are the tail multiplier and its
reciprocal from `RealInducedCharacter.data_tail` and `data_tailInv`.

A block Frobenius map commutes with compact right translation. For a skew
matrix \(X\), use the compact curve \(\exp(tX)\) in the compatibility axioms
of the two algebraic real Harish-Chandra modules. Differentiating the two
scalar evaluation curves gives the commutation with the corresponding right
derivative. Iteration gives the same commutation for every compact word.

For a polynomially bounded symbol, `exists_continuous_norm_bound_blockFrobMap`
controls the norm of its output by a continuous expression in source word
seminorms. The compact word estimate bounds any target word by finitely many
skew words. Move each of these words past the block Frobenius map and apply
the norm estimate to the derived input. This proves continuity on the
compact-finite source in the genuine smooth topology. Completeness of the
target and density of the compact-finite source give the continuous extension.

The tail symbol has polynomial growth, and its recurrence gives both compact
and Lie equivariance of the forward map. Integrating those identities gives
its group equivariance. Every nonzero value of the signed binomial symbol
has norm at least one, so its reciprocal symbol is bounded by one, with
value zero at the original zero modes. Use the compact-direction extension
for this reciprocal. The algebraic identity `tail_tailInv` makes the
composition the identity on compact-finite vectors. Density and continuity
then give the right-inverse identity on the full smooth target.
