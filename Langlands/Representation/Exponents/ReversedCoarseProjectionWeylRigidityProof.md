# Coarse projection rigidity in raw reversed upper-geometric coordinates

Authors: Workers 526, 430 and 176. Worker 526 implemented the coarse-projection
energy argument and exact statement proof. Worker 430 supplied the raw-index
monotonicity route and the inverse-reversal correction. Worker 176 adapted the
pair and expanded the coordinate and energy explanations. Imported cone-pairing
and minimal-representative uniqueness results retain their published authorship.
This is internal finite real algebra, with no new external source claim.

`Langlands.Exponents.reversedCoarseProjectionWeylRigidity` proves the exact
public
[`Langlands.Exponents.ReversedCoarseProjectionWeylRigidityStatement`](ReversedCoarseProjectionWeylRigidityStatement.md).
All natural ranks, including zero, positive ordered block shapes, one-block
shapes, zero cone vectors and arbitrary common real shifts of the strictly
decreasing real parameter are retained. There is no sign condition on that
parameter.

Write `r = B.reversePermutation`, `u = r * v` (named `w` in Lean), and
`A(a) = t(blockIndex B a)`. Multiplication is composition, so
`u(a) = r(v(a))`. The two coordinate directions from
[`ReverseBlocks`](../../Group/GL/ReverseBlocks.md) are

```text
r(B.reverse.index j a)      = B.index j.rev a,
r.symm(B.index j.rev a)     = B.reverse.index j a.
```

Thus `r` sends reversed-shape coordinates to original-shape coordinates,
whereas `r.symm` sends original-shape coordinates to reversed-shape
coordinates; both preserve positions within each block. Their block-label
forms, proved in
[`RefinedOppositePieceMinimal`](../Geometric/RefinedOppositePieceMinimal.md), are

```text
blockIndex B (r a)              = (blockIndex B.reverse a).rev,
blockIndex B.reverse (r.symm a) = (blockIndex B a).rev.
```

In particular, `u` goes from original coordinates back to original coordinates,
and `u.symm = v.symm * r.symm`. No involution identity for `r` is used.

On each source `B`-block, raw minimality makes `v` strictly increasing.
The published `blockIndex_monotone` then makes its reversed-shape target
labels nondecreasing. Reversing the labels makes them nonincreasing, and
applying the strictly decreasing `t` makes `A` after `u` nondecreasing.
The closed cone hypothesis gives zero total sum and nonnegative proper
prefix sums of `x` on that source block. Apply
`SupportedRegularWeylComparison.closedCone_pairing_antitone` to the negative
of `A` after `u`, then sum over the blocks. This gives the implemented
`hpair`, and reindexing by `u` gives `hpair'`:

```text
P := ∑ a, x(u.symm a) * A(a)
   = ∑ a, x(a) * A(u a) ≤ 0.
```

The real pairing helper is Worker 165's published finite summation-by-parts
result in [`SupportedRegularWeylConeNumerics`](SupportedRegularWeylConeNumerics.md).

Since `A(B.index i a) = t i`, the coarse-sum premise, including its factor
`(B.size i : ℝ) * t i`, says that the sum of
`x(u.symm a) + A(u.symm a) - A(a)` over target block `i` is zero.
Multiplying each such equation by `t i` and summing over all original
blocks gives `hprojpair`. Expanding it yields

```text
0 = ∑ a, (x(u.symm a) + A(u.symm a) - A(a)) * A(a)
  = P - D,
where D := ∑ a, A(a) * (A(a) - A(u.symm a)).
```

Hence `D = P ≤ 0`, which is `hbalance`. Permutation invariance gives
`∑ a, A(u.symm a)^2 = ∑ a, A(a)^2` (`hnorm`). Expanding each square and
substituting this identity proves the exact `henergy` equation:

```text
∑ a, (A(a) - A(u.symm a))^2
  = ∑ a, A(a)^2 + ∑ a, A(u.symm a)^2
      - 2 * ∑ a, A(a) * A(u.symm a)
  = 2 * ∑ a, A(a) * (A(a) - A(u.symm a))
  = 2 * D = 2 * P ≤ 0.
```

Every summand is nonnegative, so the sum and every square vanish.
This proves `A(a) = A(u.symm a)` (`hA`). Substitution of `u a` and
injectivity of the strictly decreasing `t` show that `u` preserves each
original block, hence `u ∈ blockWeyl B` (`hblock`).

The inverse reversal `r.symm` is minimal from `B` to `B.reverse`:
`reversePermutation_symm_index_strictMono` proves its source-block
condition, and the forward coordinate identity above proves its
inverse's target-block condition. These are the two actual minimality
conditions from [`WeylDefinitions`](../Geometric/WeylDefinitions.md).
Since `r.symm = v * u⁻¹` and `u⁻¹ ∈ blockWeyl B`, `v` and `r.symm`
have equal double cosets in `W_(B.reverse) \ S_n / W_B`. The public
`Geometric.weylDoubleCoset_injective`, from Worker 175's
[`WeylUniquenessProof`](../Geometric/WeylUniquenessProof.md), identifies their
minimal representatives. The conclusion is exactly
`v = B.reversePermutation.symm`. The proof uses no minimality of `u`
from `B` to `B`.

The premise is the stated coarse-sum equality, including its block-size
factor; the proof introduces no pointwise projection premise. The actual
representation-theoretic cone and coarse identities must be supplied
separately in any application. This theorem constructs no actual geometric
filtration, induction exponent transfer, grade formula, generalized-block
splitting, quotient extraction, Hom comparison or classification.
