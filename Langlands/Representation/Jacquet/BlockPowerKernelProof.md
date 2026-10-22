# The generalized compression kernel is the upper Jacquet kernel

Author: Worker 127. The short orbit-invariance helper is reproduced from
Worker 99's published `BlockCompressionProof`.

The closing theorem `Langlands.Jacquet.blockPowerKernelJacquet.{uF,uV}`
proves exactly `Langlands.Jacquet.BlockPowerKernelJacquetClause.{uF,uV}`
from `Langlands.Representation.Jacquet.CanonicalLiftStatement`.
The named theorem `blockPowerKernel_eq_jacquetKernel` exposes the equality
for any smooth representation, so it also applies under the admissibility
hypothesis of the published clause.

## Scope and conventions

The closing theorem retains every parameter of the published target: every
prime, finite p-adic field with arbitrary universe `uF`, supplied topological
data `T`, natural rank, block shape, and complex module in the independent
universe `uV`. Its representation and subgroup hypotheses are precisely
admissibility, compactness, block Iwahori factorization, and strict contraction.
Only the smoothness component of admissibility is used. The supplied topology
and its general-linear topological-group instance are installed explicitly.
There is no restriction excluding rank zero, empty or one-block shapes, or
the zero representation.

Put `N = B.unipotentSubgroup F.Carrier`, `M = B.leviSubgroup F.Carrier`,
`g = B.blockScalar F.Carrier a`, and
`C = compressedAction ρ hρ K hK g`. The proved equality is

\[
  \sup_{r\in\mathbb N}\ker(C^r)
  = \ker(\texttt{fixedJacquetMap}\;\rho\;N\;M\;h_{MN}\;K).
\]

Both sides are submodules of the existing `K`-fixed-vector space. The left
side is exactly `powerKernelSup`; the right side uses the actual upper
Jacquet quotient and common embedded Levi, with the published normalizer
inclusion. The quotient action is unnormalized, and `C` uses the normalized
compact finite-orbit average.

## Implemented proof

The private helper `average_right_invariant` proves that the compact average
of `ρ(k)v` equals that of `v` for `k ∈ K`. Multiplication by `k` and by its
inverse gives equality of the two orbit sets. Unfolding the existing
`orbitMean` then proves equality of their averages.

The private helper `relations_eventually_average_zero` works for any smooth
representation of a topological group, subgroup `N`, compact open `K`, and
element `g`. Its premise says that each `x ∈ N` is conjugated into `K` by
every sufficiently high power of `g`. It proves that every vector in the
actual relation submodule eventually has zero average after applying those
powers. `relations_eq_span` identifies that submodule with the span of
`ρ(x)w - w`. For a generator, move `ρ(g^s)` past `ρ(x)` by conjugation;
the conjugate belongs to `K` past its threshold, and average invariance
cancels the difference. Span induction treats zero and scalar multiples
directly. For addition, the maximum of the two thresholds works for every
subsequent exponent. This proves the finite-combination assertion for the
actual relation span without assuming it.

The equality theorem first shows that every pointwise power `a^r` is weakly
contracting. Induction using the published
`blockCompressedAction_mul` and the block-scalar homomorphism gives
`C^r = compressedAction ρ hρ K hK (B.blockScalar F.Carrier (a^r))`,
including exponent zero.

For each power kernel, the published `blockCompressedAction_mk` sends
`C^r v` to the action of the corresponding Levi scalar on the quotient of
`v`. That action is injective because it is the action of a group element
in a representation. Thus `C^r v = 0` forces the quotient of `v` to be zero.
The universal property of the supremum gives the first inclusion.

For the converse, `mk_eq_zero` identifies a vector in the fixed Jacquet
kernel with membership in the actual relation submodule. The published
`B.strictPowers_eventually_mem_iwahori T K` supplies the conjugation premise
for each upper-radical element; the opposite-radical input is the identity.
The span helper supplies a threshold `r` with zero average at exponent `r`.
The compression-power formula identifies this with `C^r v = 0`.
Inclusion of that power kernel in the supremum proves the other inclusion.
The closing theorem applies this equality with `hAdmissible.1`.

## Provenance

This is a derived proof from the published compression and contraction
theorems and the existing relation-span quotient. It imports
`Langlands.Representation.Jacquet.BlockCompressionProof` and
`Langlands.Group.GL.BlockContractionProof`; every existing Library pair
remains unchanged. The orbit-invariance helper is the elementary argument
from the private `average_apply_subgroup` helper in Worker 99's published
compression proof, reproduced because that declaration is private.

The motivating original is Bill Casselman, *Introduction to admissible
representations of p-adic groups*, Chapter III, *Induced representations and
the Jacquet module*, revision April 29, 2019, Lemma III.5.4 on page 6,
with operator preliminaries III.5.1–III.5.3 on pages 5–6.
Registered source: `casselman-2019-jacquet-module`; SHA256:
`377edac998669bc88da1224c4582a173854232f7fea5caf945d140ee92fde5c1`.
Retained original:
`/home/taskhub/central-library/Casselman--p-adic groups lecture notes/Introduction to representations of p-adic groups/Casselman--Chapter III - Induced representations and the Jacquet module--2019.pdf`.
Pages 5–6 were read visually to preserve the radical overbars omitted by
text extraction. No source-specific project errata file was present.

The implemented argument works directly with the normalized compact average
and unnormalized quotient action. It does not transfer Casselman's
coset-sum operator identities by assuming a scalar comparison. No Haar or
subgroup-index comparison, finite-dimensional Fitting theory, quotient
surjectivity, or canonical-lift premise is used. Stable-image bijectivity,
choice independence, and pairings are outside this theorem.
