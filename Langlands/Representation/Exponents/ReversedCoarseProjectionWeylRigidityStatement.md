# Coarse projection rigidity in reversed upper-geometric coordinates

Authors: Workers 526, 430 and 176. Worker 526 supplied the statement and
numerical argument; Worker 430 supplied the raw-index monotonicity route and
inverse-reversal correction; Worker 176 adapted the pair and its explanation.
This is an internal finite real algebra statement. It is neither a literal
source transcription nor a representation-theoretic theorem. This Lean file
defines the proposition and supplies no proof of it.

`Langlands.Exponents.ReversedCoarseProjectionWeylRigidityStatement`
quantifies over every natural rank `n`, every positive ordered block shape
`B`, every strictly decreasing real block vector `t`, every raw minimal
representative `v` from `B` to `B.reverse`, and every real diagonal vector
`x`. Minimality means that `v` increases strictly within every source
`B`-block and `v.symm` increases strictly within every target
`B.reverse`-block, as defined in
[`WeylDefinitions`](../Geometric/WeylDefinitions.md).

Write `r = B.reversePermutation`, `u = r * v` and
`A(a) = t(blockIndex B a)`. Permutation multiplication is composition:
`u(a) = r(v(a))`. The permutation `r` sends reversed-shape coordinates
to original-shape coordinates, preserving positions within each block:

```text
r(B.reverse.index j a) = B.index j.rev a.
```

This is `BlockShape.reversePermutation_index` from
[`ReverseBlocks`](../../Group/GL/ReverseBlocks.md). Its block-label form is
`blockIndex B (r a) = (blockIndex B.reverse a).rev`.
In general `r` is not its own inverse. Thus `u⁻¹ = v⁻¹ * r⁻¹`, and the
conclusion `v = r.symm` is equivalent to `u = 1`; it cannot in general be
replaced by `v = r`.

On each source `B`-block, the hypothesis puts `x` in
`IsClosedPositiveRootCone`: its sum is zero and its proper prefix sums are
nonnegative. The other hypothesis is exactly the coarse-sum identity

```text
∑ a : Fin (B.size i), ((x + A) ∘ u⁻¹)(B.index i a)
  = (B.size i : ℝ) * t i
```

for every original `B`-block `i`. These are sums of repeated diagonal
coordinates, so the block-size factor is essential. All ranks, including
zero, one-block shapes, the zero vector `x`, and arbitrary common real
shifts of `t` are retained. There is no sign condition on the entries of
`t`. No pointwise equality or minimality of `u` from `B` to `B` is assumed.

The internal numerical justification uses the closed-cone pairing
principle documented in [`Chambers`](Chambers.md). Its published
`isClosedPositiveRootCone_iff_pairing` tests monotone integer vectors;
the same finite summation-by-parts identity gives nonpositive pairing
with monotone real vectors. Source-block monotonicity of `v` makes
`blockIndex B.reverse ∘ v` nondecreasing. The block-label identity for
`r` reverses that order, and strict decrease of `t` makes `A ∘ u`
nondecreasing on each source block. Consequently
`⟨x, A ∘ u⟩ ≤ 0`, where the pairing sums products over `Fin n`.

Multiplying each coarse-sum identity by `t i`, summing over blocks and
reindexing by `u` gives
`⟨x + A, A ∘ u⟩ = ⟨A, A⟩`. Permutation invariance of the sum of
squares then gives
`∑ a, (A a - A (u a))² = 2 ⟨x, A ∘ u⟩ ≤ 0`.
Each square must vanish. Injectivity of the strictly decreasing `t`
implies `u ∈ blockWeyl B`. Hence `v = r⁻¹ * u` has the same
`B,B.reverse` Weyl double coset as `r⁻¹`. The inverse reversal is itself
minimal for these source and target shapes. The published
[`weylMinimalRepresentativeUniqueness`](../Geometric/WeylUniquenessProof.md)
then identifies `v` with `r⁻¹`. This explains the proposed assertion;
formalizing this argument is a separate proof obligation.

The public `ClosedConeStabilizerRigidityStatement` instead assumes
pointwise preservation of a shifted vector and has a different conclusion.
The present proposition supplies no actual geometric filtration,
identity-layer map, exponent transfer through induction, coarse projection
formula for actual grades, generalized-block splitting, projector, quotient
extraction, Hom comparison or classification. An application must separately
establish its numerical hypotheses for the actual representation-theoretic
objects.
