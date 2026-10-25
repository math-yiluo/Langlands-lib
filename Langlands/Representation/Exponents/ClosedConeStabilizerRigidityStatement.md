# Closed-cone rigidity of a shifted-parameter stabilizer

`Langlands.Exponents.ClosedConeStabilizerRigidityStatement` is an internal
finite-dimensional real assertion. This file states it and does not prove it.
It uses the existing ordered `BlockShape`, its actual consecutive coordinate
maps `B.index`, the block map `Geometric.blockIndex`, the actual subgroup
`Geometric.blockWeyl B`, and `Exponents.IsClosedPositiveRootCone`.

For any natural rank `n`, let `v : Fin n → ℝ` have sum zero separately on
each block of `B`. Let `t` be strictly decreasing on the ordered coarse
blocks, and let `w` permute all `n` coordinates. Assume the permuted vector
`a ↦ v (w a)` has total zero and nonnegative proper initial partial sums.
Assume also that `w` fixes the shifted vector
`a ↦ v a - t (blockIndex B a)` pointwise. The conclusion states that this
same permutation preserves every coarse block and fixes `v` pointwise.

There is no positivity hypothesis on the individual values of `t`. Common
central shifts, one-block shapes and rank zero are included. In a
representation-theoretic application, determinant exponents are repeated once
per diagonal coordinate; summing such a repeated vector over a block accounts
for block sizes. This assertion does not replace them by unweighted
split-center coordinates.

## Derivation and scope

This is a derived elementary assertion, rather than a transcription of a
literature theorem. Put `a = t ∘ blockIndex B`, and write `wv` and `wa` for
composition with `w`. The ordered consecutive numbering makes `a` antitone.
The block sums give `⟨a,v⟩ = 0`. Summation by parts for the closed positive
root cone gives `⟨a,wv⟩ ≥ 0`. The shifted-vector equation gives
`a - wa = v - wv`, hence `⟨a,a - wa⟩ ≤ 0`. Coordinate permutation preserves
the sum of squares, so

`∑ j, (a j - wa j)^2 = 2 ⟨a,a - wa⟩`.

The left side is nonnegative. It must vanish, giving `a = wa`.
Strict decrease of `t` then identifies the coarse block containing every
coordinate, and the shifted-vector equation gives `v = wv`.
This is a proposed proof route for the stated assertion.

The assertion isolates a numerical step useful in the supported regular
Jacquet comparison. It assumes the specific cone condition for the specific
permutation being tested. It supplies no actual cuspidal occurrence, analytic
continuation, collision persistence, character comparison, finite-length
statement or Jacquet multiplicity theorem. Those applications need separate
proofs establishing these hypotheses.

The existing `orthogonalParameterComparison` treats two orthogonal pairs with
two nonnegative cross pairings. The present criterion instead uses one cone
pairing together with invariance of a permutation norm. The separate ordered
block-parameter rigidity task compares two block shapes after a coordinate
equality; here the conclusion is membership of the given permutation in the
actual coarse Weyl subgroup.
