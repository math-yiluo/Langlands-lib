# Supported recovery and arbitrary-tempered quotient reflection

Author: Worker 1080.

`Langlands.glRelativeRecovery` proves the exact current Library proposition
`Langlands.GLRelativeRecoveryStatement.{uF,uV,uM,uW,uX,uZ}`. Its entire
type is that proposition, with six independent universes and no additional
premise. It pairs the two proved components, whose different support scopes
are preserved.

`glSupportedRelativeRecovery` retains the fixed fine and middle data and
all actual support surjections to the irreducible tempered coarse input.
The competing coarse input is any irreducible admissible quotient of the
same fine inner induction. From two actual outer surjections onto one
irreducible target it recovers equivalence of the untwisted coarse inputs.
Its implemented strict-multiplicity proof is described in
[SupportedRelativeRecoveryProof.md](SupportedRelativeRecoveryProof.md).
The supported all-regular theorem constructs equal positive inner and
ambient fine-Jacquet counts. Second adjointness embeds both coarse inputs
in the common quotient's opposite Jacquet module. If they were inequivalent,
refined exactness, the actual binary-product comparison and finer Jacquet
transitivity would embed the product of their inner Jacquet modules in its
composed Jacquet module. Actual kernel-series decomposition and additive
multiplicities would then force `m + mθ ≤ mJ ≤ m` with `mθ > 0`, a
contradiction. The competitor is never assumed tempered.

`glTemperedRelativeQuotientReflection` starts with arbitrary irreducible
analytically tempered coarse input and assumes no middle or fine support
map for it. Its implemented proof is described in
[TemperedRelativeQuotientReflectionProof.md](TemperedRelativeQuotientReflectionProof.md).
The public actual-quotient Hom comparison supplies finite-dimensional Hom
spaces of equal finrank at the ambient twisted and inner untwisted levels.
The given fine ambient quotient makes the first Hom space nonzero by
proved standard second adjointness and the actual flattened/composed
opposite-Jacquet comparison. Positivity of finrank transfers to the inner
space. Proved refined second adjointness and coarse irreducibility then
supply the required actual surjection from fine inner induction. The
comparison's independent geometric-filtration and tempered-exponent proof,
including extraction on this actual quotient and finer Jacquet transitivity,
replaces the selected-branch continuation step; no unproved comparison or
continuation assertion is a premise.

This is an internal assembly of the derived GL_n forms of A. J. Silberger,
*The Langlands quotient theorem for p-adic groups* (1978), Propositions
5.7 and 5.8, printed pp.101–102. The support setup is on p.99 and the
normalizations on pp.96–97. The registered original is
`provided-5423f8a28c0b7ad5a7f9a07a3d55d399d5162a798fecd70bf11a5d75fa8b9354`,
SHA256 `4f437d7ee21c65e43ede0a34b9a6b274cf4d947c23ad7637976bd38fd72fdac5`.
Worker 1080 read the full article and inspected the relevant formula images.
The unrestricted wording of Lemma 5.3 is not invoked for unsupported input.

Both components use actual surjective intertwining maps, with arbitrary
irreducible outer quotient carriers. Positive rank, all strictly decreasing
real coarse parameters and every central shift are retained. Upper
normalized induction uses right translation and positive-half-modulus
covariance; opposite Jacquet normalization uses the positive upper
half-modulus. Absolute values are `q^(-valuation)` and the fine determinant
twist is `-vB + restrict(t)`. There is no chosen canonical quotient,
identification of universes, additional support premise, new axiom or
assumption of a downstream Langlands classification theorem. The target
pair and its imports are unchanged.
