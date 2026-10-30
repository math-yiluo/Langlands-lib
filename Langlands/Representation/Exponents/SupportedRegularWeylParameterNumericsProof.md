# Proof of the supported regular Weyl numerical unit

Author: Worker 165. Worker 960 adapted the assembly to the published
statement, whose second clause returns the antitone conclusion as an
implication from `StrictAnti t`.

`Langlands.Exponents.supportedRegularWeylParameterNumerics` proves exactly
`Langlands.Exponents.SupportedRegularWeylParameterNumericsStatement`.
It assembles the internal helper proofs in
`SupportedRegularWeylConeNumerics` and `SupportedRegularWeylParameterCones`.
Those paired Markdown files describe the implemented arguments in detail.

For the first clause, the proof reuses
`Langlands.Exponents.diagonal_cone_of_weighted_block_cone` from
`WeightedBlockCone`, extracted from the existing opposite-twist cone proof.
Its statement is identical to the weighted lifting clause. Block sums preserve
the zero total and establish every boundary inequality; constancy within
blocks lets the existing partial-sum interpolation give every interior cut.

For the second clause, the published `positiveRootParameterCone` supplies
the size-weighted open cone on each middle block. Weakening to the closed
cone and applying weighted lifting gives each middle-block cone.
Concatenation through the block-coordinate equivalence gives the full
diagonal cone, including the literal shape-equality transport.
`positiveRootBlockSums` supplies zero sums on every coarse block, so the
pairing with any coarse-block-constant vector vanishes. Repetition of a
strictly decreasing coarse vector is antitone by monotonicity of the
coarse block index.

For the third clause, put `x = V1 o s.symm` and `a = A1 o s.symm`.
The first fixed relation gives the identity

`sum (x-V2)^2 = sum V2^2 - sum V1^2 + 2*sum x*a - 2*sum x*A2`.

Permutation invariance transports the first orthogonality identity to
`sum x*a = 0`. The cone of `x` and antitonicity of `A2` give
`sum x*A2 >= 0` by summation by parts. Since the squared distance is
nonnegative, `sum V1^2 <= sum V2^2`. Applying the same argument with the
second, independent permutation gives the reverse inequality. The
squared distance is therefore zero, and each nonnegative square
vanishes. This proves `V1 (s.symm i) = V2 i`. Evaluating at `s i`
identifies `V2 o s` with the original `V1`, whose assumed cone gives the
inverse cone using the first permutation.

This is finite-coordinate algebra. The theorem does not produce the
one-sided cone comparisons or their fixed relations, and it asserts no
Jacquet occurrence or continuation result. It permits all ranks and
arbitrary coarse central shifts.
