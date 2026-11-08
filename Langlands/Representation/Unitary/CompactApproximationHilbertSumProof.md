# Proof of the actual equivariant Hilbert sum

Worker 116 implements `Langlands.Analysis.compactApproximationHilbertSum`
with type exactly `Langlands.Analysis.CompactApproximationHilbertSumStatement`.
The arbitrary group and Hilbert-space universes are independent. All subspaces,
operators, sums and group actions are the actual objects in the target.

The preceding orthogonal-family theorem supplies a set A of actual nonzero
minimal closed invariant submodules of W, pairwise orthogonal with closed
algebraic sum W. Closedness makes every summand complete. Mathlib's
`OrthogonalFamily.linearIsometry` sends the actual `lp` family with exponent 2
to the unconditional sum of its inclusions in E. Its range theorem identifies
that range with the closure of the supremum of the summand inclusions. The
range of a subtype inclusion is the original submodule, so this range is W.

Corestrict this summation linear map to W. The inherited norm makes it a
linear isometry, and the range equality proves it surjective. Mathlib's
`LinearIsometryEquiv.ofSurjective` supplies U without changing its forward
map. The orthogonal-family sum and single-supported-vector formulae therefore
give exactly the two canonical summation properties required in the target.

Restrict each original operator π(g) to W, and conjugate that bounded operator
by U and its inverse. This constructs an actual bounded endomorphism of the
external sum. Its identity and multiplication laws follow by applying U,
cancelling U with its inverse, and using the original homomorphism laws.
Thus these operators form the actual homomorphism ρ, and U intertwines its
action with π on W.

For each g and square-summable vector v, form the family w whose P-coordinate
is π(g) applied to v's P-coordinate. Invariance puts it in the same summand.
Inner-product preservation gives norm preservation, so `Memℓp.mono'` proves
that w is square summable. Applying the bounded operator π(g) to the
canonical convergent sum of v gives the canonical sum of w. Uniqueness of
sums and the already proved intertwining identity imply U(w)=U(ρ(g)v).
Injectivity of U proves w=ρ(g)v, giving the literal coordinate formula.
Finally U preserves inner products and the original action does as well;
these two identities prove inner-product preservation by ρ.

The source motivation is the direct-sum paragraph of Getz–Hahn (2024),
Lemma 9.3.1, printed p.247, one-based PDF p.259, registered source
`getz-hahn-2024-automorphic-representations`, SHA-256
`a125cf9c0f445972cbbd3552b4fb9905ca948108a05880f90eaa43558d09a507`.
The complete October 2026 author errata is registered as
`getz-hahn-2024-errata-2026-10`, SHA-256
`e641ec2a5485443f792935afe5ae4940323755968f784ce290a96d9cd76fc1c2`,
and has no entry for that lemma. The statement Markdown records the exact
internal extraction and original-source correspondence. This implementation
completes its canonical external-sum and equivariance details using Mathlib's
actual orthogonal-family summation. There is no separability or countability
assumption, and the empty family handles W=0. Finite representation
multiplicity, integrated-operator compatibility and the construction of any
automorphic Hilbert space remain separate obligations. Worker 1467 adopts Worker 116’s proof in the focused exact-target proof task,
using the published target and predecessor theorems without changing them.
