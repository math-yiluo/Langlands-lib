# Proof: strict block-length growth for concrete conjugate pair refinements

Author: Worker 277.

The theorem `Langlands.conjugatePairRefinementRank.{uF}` has type exactly
`Langlands.ConjugatePairRefinementRankStatement.{uF}`. The statement module
`Langlands.Group.GL.ConjugatePairRefinementRankStatement` is imported by name
and is not changed. For every field `K : Type uF` with `[Infinite K]` and
every `n : ℕ`, the theorem proves both conjuncts. First, for all
`P Q : Langlands.Exponents.ConjugateBlockPair n K`,
`Q.StrictlyRefines P → P.shape.length < Q.shape.length`. Second, every `P`
satisfies `P.shape.length ≤ n`. Both conjugating matrices are arbitrary.
Rank zero, repeated block sizes and one-block shapes are included, and no
standardness or consecutive-refinement hypothesis is added. The hypothesis
`Q.StrictlyRefines P` is used as defined in `ParabolicPair`:
`Q.parabolic ≤ P.parabolic`, `P.splitComponent ≤ Q.splitComponent`, and
failure of the reverse pair of inclusions.

The only use of infinitude is to choose `t : K` with `t ≠ 0` and `t ≠ 1`,
via `Infinite.exists_notMem_finset {0, 1}`. The auxiliary results that need it take
the weaker hypothesis `∃ t : K, t ≠ 0 ∧ t ≠ 1`. The proof uses no topology,
valuation, representation or Library proof module. Besides the statement
module (which imports `ParabolicPair`), it imports only Mathlib's
transvection matrices, finite-dimensional linear algebra and `Set.ncard`.
Auxiliary declarations live in the namespace
`Langlands.ConjugatePairRefinementRankProof`.

## Standard coordinates

For a block shape `B`, `blk B x` is the block containing the standard
coordinate `x`, namely `(B.indexEquiv.symm x).1`. `firstIndex B i` is the
coordinate `B.index i ⟨0, _⟩`; it exists because block sizes are positive.
`mem_parabolic_iff_blk` restates `BlockShape.mem_parabolic_iff`: `g` lies
in the standard parabolic iff `g x y = 0` whenever `blk B y < blk B x`.

The shared `BlockShape.length_le` from `Langlands.Group.GL.Blocks` supplies
the second conjunct. Its proof compares
`B.length = ∑ i, 1` with `∑ i, B.size i = n`, using `B.positive`.

## Split components and their linear spans

`scalarLinear B : (Fin B.length → K) →ₗ[K] Matrix (Fin n) (Fin n) K` sends
`a` to `diagonal (fun x => a (blk B x))`. It is injective: evaluate at
`firstIndex B i`. For a pair `P` with conjugator `c`, `pairLinear P a` is
`c * scalarLinear P.shape a * c⁻¹`. It is injective because conjugation by
`c` cancels. By `coe_scalarMap`, `BlockShape.coe_blockScalar` identifies the
actual matrix of `P.scalarMap a` with `pairLinear P (fun i => (a i : K))`.

`splitSpan P` is the `K`-linear span of the matrices of the actual subgroup
`P.splitComponent`. `splitSpan_eq` shows `splitSpan P = range (pairLinear P)`.
One inclusion is `coe_scalarMap`. For the other, write a vector as
`∑ i, v i • Pi.single i 1`. Let `a` be the unit vector equal to `t` at `i`
and `1` elsewhere. Then `Pi.single i 1 = (t - 1)⁻¹ • (a - 1)` coordinatewise,
so `pairLinear P (Pi.single i 1)` is a combination of the split-component
matrices `P.scalarMap a` and `P.scalarMap 1`. This is where
`t ∉ {0, 1}` is needed. By injectivity, `finrank_splitSpan` gives
`finrank K (splitSpan P) = P.shape.length`.

`mem_splitComponent_of_mem_range` recovers group elements. Suppose
`g : GL_n(K)` has matrix `pairLinear P v`. Its determinant is nonzero and
equals `det c * det D * det c⁻¹` for `D = scalarLinear P.shape v`, so
`det D ≠ 0`. As `det D` is the product of the `v (blk x)` and block `i`
contains `firstIndex P.shape i`, every `v i ≠ 0`. Hence
`g = P.scalarMap (fun i => Units.mk0 (v i) _)` lies in `P.splitComponent`.

Consequences:

- `length_le_of_splitComponent_le`: `P.splitComponent ≤ Q.splitComponent`
  makes `splitSpan P ≤ splitSpan Q`, so `P.shape.length ≤ Q.shape.length`
  by `Submodule.finrank_mono`.
- `splitComponent_le_of_length_eq`: if also the lengths are equal, the spans
  are equal (`Submodule.eq_of_le_of_finrank_eq`). Every element of
  `Q.splitComponent` then has matrix in `range (pairLinear P)`, so it lies in
  `P.splitComponent`.

## Flags preserved by the parabolics

`flag B m` is the subspace of `Fin n → K` of vectors vanishing at every
coordinate `x` with `m ≤ blk B x`. Then `flag B 0 = ⊥` and
`flag B B.length = ⊤`. The proved facts for the standard parabolic are:

- `mulVec_mem_flag`: each standard parabolic element maps every `flag B m`
  into itself, because its entries below the block diagonal vanish.
- `mem_parabolic_of_flag`: a matrix preserving every `flag B m` with
  `m ≤ B.length` lies in the standard parabolic. Its column `y` is the image
  of `Pi.single y 1 ∈ flag B (blk B y + 1)`.
- `flag_injective`: for `m < m' ≤ B.length`, the coordinate vector at
  `firstIndex B ⟨m, _⟩` lies in `flag B m'` but not in `flag B m`.
- `exists_parabolic_shift`: suppose `blk B q ≤ blk B x`. Then some `g` in
  the standard parabolic and some `s ≠ 0` satisfy
  `g *ᵥ u - u = (s * u x) • Pi.single q 1` for all `u`. For `q ≠ x`, `g` is
  the transvection `1 + single q x 1` (determinant `1`) and `s = 1`. For
  `q = x`, `g` is `diagonal (Function.update 1 x t)` (determinant `t`) and
  `s = t - 1`. This again uses `t ∉ {0, 1}`.
- `eq_flag_of_invariant`: every subspace `U` invariant under the standard
  parabolic equals `flag B m` for some `m ≤ B.length`. Take the least `m`
  with `U ≤ flag B m` (`Nat.find`). If `m = 0`, then `U = ⊥`. Otherwise
  `U ≰ flag B (m - 1)`, which gives `u ∈ U` and `x` with `blk B x = m - 1`
  and `u x ≠ 0`. Write `v ∈ flag B m` as `∑ q, v q • Pi.single q 1`. Each
  `q` with `v q ≠ 0` has `blk B q ≤ blk B x`. Then
  `exists_parabolic_shift` puts a nonzero multiple of `Pi.single q 1` into
  `U`, so `v ∈ U`.

For a pair `P` with conjugator `c`, `pairFlag P m` is the comap of
`flag P.shape m` along `toLin' c⁻¹`: `v ∈ pairFlag P m` iff
`c⁻¹ *ᵥ v ∈ flag P.shape m`. `mem_parabolic_iff_conj` characterizes
`g ∈ P.parabolic` by `c⁻¹ * g * c ∈ P.shape.parabolic K`. Conjugation
transports the four facts above (`mulVec_mem_pairFlag`,
`mem_parabolic_of_pairFlag`, `eq_pairFlag_of_invariant`,
`pairFlag_injective`) to the actual parabolic `P.parabolic`.

`parabolic_le_of_length_eq` proves that `Q.parabolic ≤ P.parabolic` and
`P.shape.length = Q.shape.length` imply `P.parabolic ≤ Q.parabolic`. Let
`SP` be the set of subspaces `pairFlag P m` for `m : Fin (P.shape.length + 1)`,
and define `SQ` in the same way. Every member of `SP` is invariant under
`P.parabolic`, hence under `Q.parabolic`. So it belongs to `SQ`
(`eq_pairFlag_of_invariant` for `Q`). By injectivity, `SP` and `SQ` have
`P.shape.length + 1` and `Q.shape.length + 1` elements. Equal lengths
therefore give `SP = SQ` (`Set.eq_of_subset_of_ncard_le`). An element of
`P.parabolic` preserves every member of `SP = SQ`, so it lies in
`Q.parabolic` by `mem_parabolic_of_pairFlag`.

## Conclusion

`length_lt_of_strictlyRefines` combines these results. From
`P.splitComponent ≤ Q.splitComponent`,
`P.shape.length ≤ Q.shape.length`. Suppose the lengths were equal. Then
`parabolic_le_of_length_eq` and `splitComponent_le_of_length_eq` give
`P.parabolic ≤ Q.parabolic` and `Q.splitComponent ≤ P.splitComponent`. That
is exactly `P.Refines Q`, which strictness excludes. Hence
`P.shape.length < Q.shape.length`. The final theorem obtains `t` from
`[Infinite K]` and pairs this with `BlockShape.length_le`. Equality of lengths thus
forces equality of the actual subgroups, not of the chosen presentations.

## Provenance

This is derived type-A linear algebra, not a quoted theorem. The context is
A. J. Silberger, *Introduction to harmonic analysis on reductive p-adic
groups* (1979), registered as `silberger-1979-harmonic-analysis`, section
0.3, printed pp.5–6 (one-based PDF pp.11–12). That section defines parabolic
pairs, their p-rank and their ordering, as recorded in the statement's
Markdown. The proof route (dimensions of split-component spans and invariant
flags) is this module's own. No weakly critical support, tempered support or
exhaustion, critical-to-minimal converse, regular exhaustion, equal-exponent
grouping or other representation-theoretic result is used.
