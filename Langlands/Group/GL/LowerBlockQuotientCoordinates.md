# Lower-block coordinates on the actual left unipotent quotient

This module descends the published lower-block display `lowerBlockPair g x h`
of `Langlands.Group.GL.LowerBlockLocalizationCoordinates` to a map of left
coset spaces

```text
LeftQuotient (upperUnipotent a R) × Matrix (Fin d) (Fin a) R × lowerTriangularSubgroup d R
  → LeftQuotient (upperUnipotent (a + d) R),
  ([g], x, h) ↦ [[[g, 0], [x, h]]].
```

It proves that the map is well defined, injective and jointly continuous, and
defines the actual range with an inverse on it. All declarations are in the
namespace `Langlands.GeneralLinear`.

## Source and provenance

The construction is derived coordinate infrastructure, not a verbatim source
assertion. It comes from H. Jacquet, I. I. Piatetski-Shapiro and
J. A. Shalika, *Rankin-Selberg convolutions*, American Journal of Mathematics
105 (1983), section 9.3, printed pages 456–457 (one-based PDF pages 91–92).
The registered source is `jpss-1983-rankin-selberg`, kept at
`/home/taskhub/central-library/Jacquet-Piatetski-Shapiro-Shalika--Rankin-Selberg Convolutions--1983.pdf`,
SHA-256 `d9feed6388ca5acf02ecc6a8cce984871a7c28f062ff441e45a71fa2d8962245`.
Both rendered pages were read. No erratum specific to this source was found
in the project's literature records. This is not a claim that no erratum
exists elsewhere.

In the case `r₂ < t < r` on printed page 456, the source writes
`Ψ(s, W, W'; 0)` as an integral of
`W[[g,0,0],[x,h,0],[0,0,1]] W'[[g,0],[x,h]]` and states "where
`g ∈ N_{r₂}\G_{r₂}`, `h ∈ B̄_{t−r₂}`". The coordinates `(g, x, h)` stand
for a point of `N_t\G_t`, represented by the matrix `[[g,0],[x,h]]` of rank `t`.
Here `a = r₂` and `d = t − r₂`. This module formalizes only that coset-level
coordinate map. It does not include the integral, the measure `dg d_r(h) dx`,
or the claim that the image has full measure.

The source calls the parameter space of `x` `M(r₂ × (t − r₂), F)`. However,
the displayed block lies below `g`, so it has `t − r₂` rows and `r₂` columns.
As in the published `lowerBlockPair`, `x : Matrix (Fin d) (Fin a) R` is this
displayed block, with no transpose.

## Conventions

`LeftQuotient H` is the published `QuotientIntegration.LeftQuotient H`,
that is `Quotient (QuotientGroup.rightRel H)`. Its points are left cosets
`H * k`, and `Quotient.mk _ k = Quotient.mk _ k'` holds exactly when
`k' * k⁻¹ ∈ H`. This is the theorem `leftQuotient_mk_eq_iff`, stated for an
arbitrary group and subgroup.

`upperUnipotent n R` is the published subgroup of upper triangular matrices
with unit diagonal. `lowerTriangularSubgroup d R` is the published subgroup of
invertible lower triangular matrices, written `B̄_d` in the source.
`lowerBlockPair g x h` is the matrix `[[g,0],[x,h]]` in the standard
consecutive coordinates `Fin (a + d)`. Rows and columns `0, …, a−1` form the
first block and `a, …, a+d−1` the second, through `finSumFinEquiv`.

The coefficient ring is an arbitrary `R : Type u` with `CommRing R`. Every
field in any universe is a special case. The ranks `a` and `d` are arbitrary
natural numbers, so the positive ranks in the task are covered. No field
hypothesis or positivity is used.

## Matrix and subgroup laws

- `matrix_eq_one_of_triangular`: a square matrix over `Fin n` that is both
  `IsUpperTriangular` and `IsLowerTriangular` and has every diagonal entry `1`
  equals `1`. The proof compares entries by trichotomy of the indices.
- `lowerBlockPair_val_submatrix`: reading `lowerBlockPair g x h` through
  `finSumFinEquiv` on rows and columns gives exactly
  `Matrix.fromBlocks g.val 0 x h.val.val`.
- `rankInclusion_val_submatrix`: likewise the published
  `rankInclusion d u = diag(u, I_d)` gives `Matrix.fromBlocks u.val 0 0 1`.
- `rankInclusion_mem_upperUnipotent`: if `u ∈ upperUnipotent a R`, then
  `rankInclusion d u ∈ upperUnipotent (a + d) R`. The proof checks the entries
  of each of the four blocks.
- `rankInclusion_mul_lowerBlockPair`:
  `rankInclusion d u * lowerBlockPair g x h = lowerBlockPair (u * g) x h`.
  The proof multiplies the block matrices with `Matrix.fromBlocks_multiply`.

## Uniqueness

`lowerBlockPair_eq_of_upperUnipotent_mul` is the central algebraic fact. Let
`u ∈ upperUnipotent (a + d) R` with
`u * lowerBlockPair g x h = lowerBlockPair g' x' h'`. Then

```text
g' * g⁻¹ ∈ upperUnipotent a R,   x' = x,   h' = h,
u = rankInclusion d (g' * g⁻¹).
```

The proof reads `u` through `finSumFinEquiv` as `[[A,B],[C,D]]` and compares the
four blocks of `[[A,B],[C,D]] * [[g,0],[x,h]] = [[g',0],[x',h']]`:

- `C = 0`, because `C` consists of entries of `u` strictly below the diagonal.
- `B * h = 0`, and `h` is invertible, so `B = 0`.
- `D * h = h'`, so `D = h' * h⁻¹` is lower triangular. `D` is also a diagonal
  block of `u`, hence upper triangular with unit diagonal, so
  `matrix_eq_one_of_triangular` gives `D = 1`.
- Then `x' = C * g + D * x = x`, `h' = D * h = h` and `g' = A * g`. So
  `(g' * g⁻¹).val = A`, an upper triangular diagonal block of `u` with unit
  diagonal. Reassembling the blocks gives `u = diag(A, I_d)`.

## Representative independence and the descended chart

- `leftQuotient_mk_lowerBlockPair_mul`: for `n ∈ upperUnipotent a R`, the coset
  of `lowerBlockPair (n * g) x h` equals the coset of `lowerBlockPair g x h`.
  The proof writes `lowerBlockPair (n * g) x h` as
  `rankInclusion d n * lowerBlockPair g x h` and uses
  `rankInclusion_mem_upperUnipotent` for `n⁻¹`.
- `leftQuotient_mk_lowerBlockPair_eq_iff`: the cosets of
  `lowerBlockPair g x h` and `lowerBlockPair g' x' h'` agree exactly when
  `[g] = [g']` in `LeftQuotient (upperUnipotent a R)`, `x = x'` and `h = h'`.
  The forward direction applies the uniqueness theorem to
  `u = lowerBlockPair g' x' h' * (lowerBlockPair g x h)⁻¹`. The reverse
  direction is the previous lemma.
- `LowerBlockQuotientParameters a d R` abbreviates
  `LeftQuotient (upperUnipotent a R) × Matrix (Fin d) (Fin a) R ×
  lowerTriangularSubgroup d R`.
- `lowerBlockQuotientChart` is defined with the published
  `QuotientIntegration.descend`. On the first factor it descends
  `g ↦ [lowerBlockPair g x h]`, and the invariance proof is
  `leftQuotient_mk_lowerBlockPair_mul`. So the map is well defined through an
  actual proof, not through a chosen coset representative.
- `lowerBlockQuotientChart_mk` is the representative evaluation equation
  `lowerBlockQuotientChart ([g], x, h) = [lowerBlockPair g x h]`. It holds by
  `rfl`.
- `lowerBlockQuotientChart_injective` follows from the forward direction of
  `leftQuotient_mk_lowerBlockPair_eq_iff`, after choosing representatives of
  the two first coordinates by quotient induction.

## Range and inverse

- `lowerBlockQuotientRange a d R` is `Set.range lowerBlockQuotientChart`,
  the actual range. This module does not claim that the range is all of
  `LeftQuotient (upperUnipotent (a + d) R)`, that it is open, or that it has
  full measure.
- `mem_lowerBlockQuotientRange_iff`: a coset is in the range exactly when it is
  the coset of some `lowerBlockPair g x h`.
- `mk_mem_lowerBlockQuotientRange_iff`: the coset of `k` is in the range exactly
  when `n * k = lowerBlockPair g x h` for some `n ∈ upperUnipotent (a + d) R`
  and parameters `g`, `x`, `h`.
- `lowerBlockQuotientEquivRange` is `Equiv.ofInjective` applied to the chart
  and its injectivity proof. `lowerBlockQuotientEquivRange_apply` says that its
  value is the chart.
- `lowerBlockQuotientInverse q` is `lowerBlockQuotientEquivRange.symm q` for
  `q` in the range. Its value is the unique parameter mapping to `q`, so it is
  determined by the proved injectivity. It does not depend on a choice of coset
  representatives.
- Inverse laws: `lowerBlockQuotientInverse_chart` proves
  `lowerBlockQuotientInverse ⟨chart p, _⟩ = p`, and
  `lowerBlockQuotientChart_inverse` proves `chart (lowerBlockQuotientInverse q) = q`.
- `lowerBlockQuotientInverse_mk` evaluates the inverse at the coset of
  `lowerBlockPair g x h` as `([g], x, h)`. `lowerBlockQuotientInverse_eq_iff`
  says that `lowerBlockQuotientInverse q = p` holds exactly when
  `lowerBlockQuotientChart p = q`.

## Rank transport

A consumer may need the ambient rank in a different form, for example
`a + d = n + 1` for `RankinSelberg.LeftUnipotentQuotient n F`, which is
`LeftQuotient (upperUnipotent (n + 1) F)`. The following declarations handle
this transport.

- `reindex_finCongr_apply`: `reindex (finCongr hmn) k i j` is the entry of
  `k` at the cast indices. The natural-number coordinates do not change.
  This shared lemma is imported from [`RankReindex`](RankReindex.md).
- `reindex_finCongr_mem_upperUnipotent_iff`: reindexing along
  `finCongr hmn`, for `hmn : m = n`, preserves and reflects membership in
  `upperUnipotent`.
- `upperUnipotentQuotientCongr hmn` is a homeomorphism
  `LeftQuotient (upperUnipotent m R) ≃ₜ LeftQuotient (upperUnipotent n R)`,
  built from `Homeomorph.Quotient.congr` and the published
  `reindexContinuous (finCongr hmn)`. It needs only `TopologicalSpace R`.
  `upperUnipotentQuotientCongr_mk` sends the coset of `k` to the coset of
  `reindex (finCongr hmn) k`.

## Continuity

Under `[TopologicalSpace R] [IsTopologicalRing R]`, which every topological
field satisfies:

- `continuous_lowerBlockPair`: the raw display
  `(g, x, h) ↦ lowerBlockPair g x h` is jointly continuous on the published
  `LowerBlockParameters a d R`. By `Units.continuous_iff`, the value matrix and
  the inverse matrix must both be continuous. The value matrix is a reindexed
  block matrix. The inverse matrix, by the published `lowerBlockPair_inv`, has
  blocks `g⁻¹`, `0`, `-h⁻¹ * x * g⁻¹` and `h⁻¹`. Each block is continuous, so
  the inverse matrix is too. Continuity of inversion in `R` is not used.
- `continuous_lowerBlockQuotientChart`: the descended chart is jointly
  continuous for the quotient topology on `LeftQuotient (upperUnipotent a R)`
  and the product topology. The map `Prod.map (leftQuotientMap _) id` is an open
  quotient map, by the published `leftQuotient_isOpenQuotientMap` and
  `IsOpenQuotientMap.prodMap`. The chart composed with it is the continuous
  `leftQuotientMap ∘ lowerBlockPair`.

## Scope

This is a single definitions/construction unit. It does not prove that the
range is open, that it has full measure, or that the inverse map is
continuous. It contains no quotient integration formula, Jacobian, measure
compatibility or intermediate-span conclusion. No structure assumes
injectivity or any of these properties. These belong to separate later tasks.
