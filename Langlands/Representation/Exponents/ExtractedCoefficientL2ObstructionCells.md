# Countably many disjoint cells below a diagonal uniformizer element of `GL_n`

Author: Worker 819.

This module supplies the analytic lower bound used in the proof of
`Langlands.GLExtractedCoefficientL2ObstructionStatement`
(see [`ExtractedCoefficientL2ObstructionProof`](ExtractedCoefficientL2ObstructionProof.md)).
It contains internal helper lemmas only; none of them is a published statement.
The idea is the double-coset volume and lattice-summability argument cited in
the statement Markdown: Casselman 1995, Proposition 1.5.2 and §4.4 (literature
ID `casselman-1995-admissible-representations`). This module does not prove a
Haar-volume estimate. Instead it counts explicit disjoint translates by
abelian unipotent elements inside the double cosets. This explicit route is
internal to this project.
The module reuses the unipotent, digit and integrality lemmas of the published
module `Langlands.Representation.Classification.ProductLeviNecessityCells`.
These are `Pairs`, `unip`, `inv_mul_unip_mul`, `le_one_of_unip_eq`, `digitVal`,
`eq_of_level_digitVal_sub` and `continuous_unip`.

Throughout, `S : Finset (Fin n)` and `g ∈ GL_n(F)` is the diagonal matrix with
the uniformizer `ϖ` at the indices in `S` and `1` elsewhere. `K` denotes the
integral subgroup `CartanQuotient.maximalCompact T n`.

## Small unipotent elements

`exists_unip_mem`: for every open subgroup `K'` of `GL_n(F)` there is `t : ℕ`
such that `unip S (ϖ ^ t X)` lies in `K'` for every integral tuple `X`. The
proof uses continuity of `unip S` at `0`, the product neighbourhood filter and
`T.exists_additiveLattice_subset` in each coordinate. It is the `GL_n` version
of the product-Levi lemma of the same name.

## The diagonal element and integral matrices

- `pow_val_eq_diagonal`: `g ^ M` is the diagonal matrix with `ϖ ^ M` on `S`
  and `1` elsewhere.
- `uniformizerUnit_pow_value`, `pow_val_le_one`: `ϖ ^ M` has valuation
  `exp (-M)`, so all entries of `g ^ M` are integral.
- `le_one_mul_apply`: products of matrices with integral entries have
  integral entries.
- `valuation_det_eq_one`: elements of `K` have determinant of valuation one.
  This is the published `valuation_det_integralRange`.
- `valuation_det_pow`: `det (g ^ M)` has valuation `exp (-(|S| M))`.

## Disjointness across exponents

`le_of_mk_eq`: let `S` be nonempty and `b ∉ S`. If `u g ^ M k` and
`u' g ^ M' k'`, with `u, u', k, k' ∈ K`, have the same image modulo the
centre, then `M' ≤ M`. Write the central quotient
`(u g ^ M k)⁻¹ (u' g ^ M' k')` as the scalar `z`. Then

`g ^ M' = (u'⁻¹ u) g ^ M (k k'⁻¹) z`.

The `(b, b)` entry of the left side is `1`. On the right it is an integral
entry times `z`, so `1 ≤ v(z)`. The determinant valuations then give
`exp (-(|S| M')) = exp (-(|S| M)) v(z) ^ n ≥ exp (-(|S| M))`, so
`|S| M' ≤ |S| M`. Since `|S| > 0`, this gives `M' ≤ M`. Applying the lemma in
both directions shows that the cells of different exponents are disjoint.

## Disjointness for one exponent

`level_of_mk_eq`: if `unip S Y g ^ M k` and `unip S Y' g ^ M k'`, with
`k, k' ∈ K`, have the same image modulo the centre, then every coordinate of
`Y' - Y` has level `M`. The proof conjugates the unipotent difference by
`g ^ M` with `inv_mul_unip_mul` and applies `le_one_of_unip_eq`. It is the
`GL_n` version of the product-Levi lemma of the same name.

## The countable cell sum

`cells_tsum_lt_top`: let `S` and `Sᶜ` be nonempty, `h₀ ∈ GL_n(F)`, `KP` an
open subgroup contained in `K`, and `μ` a left-invariant measure on the actual
central quotient for any Borel measurable structure. Let `f` be in `L²(μ)`, and
let `F0 M ≤ ‖f‖ₑ` on every image of `h₀ u g ^ M k` with `u, k ∈ KP`. Then there
is `t : ℕ` with

`∑' m, q ^ (m |S| |Sᶜ|) * (F0 (m + t) ^ 2 * μ (mk '' KP)) < ⊤`.

The index type is `Σ m : ℕ, (Pairs S → Fin m → ResidueField)`. The cell of
`⟨m, δ⟩` is the left translate of `mk '' KP` by
`h₀ * unip S (ϖ ^ t * digitVal δ) * g ^ (m + t)`, where `t` comes from
`exists_unip_mem` for `KP`. The cells are open, hence measurable, and each has
measure `μ (mk '' KP)` by left invariance. They are pairwise disjoint: cancel
`h₀`, use `le_of_mk_eq` twice to get equal exponents, then `level_of_mk_eq`
and `eq_of_level_digitVal_sub` to get equal digits. The cells are not assumed
to cover the quotient. The published `Langlands.countableCellLpLower` at
exponent `2` makes the weighted sum over the cells finite. Since the fibre over
`m` has `q ^ (m |S| |Sᶜ|)` elements, rewriting the sum over the sigma type
gives the stated inequality.
