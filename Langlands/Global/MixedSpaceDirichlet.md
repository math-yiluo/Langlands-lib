# Simultaneous Dirichlet approximation at the infinite places

This supporting module proves a uniform Dirichlet approximation theorem for
the infinite part of an arbitrary number field `F` in universe `u`. It is a
preparatory analytic estimate for the rank-two (Gauss) step of the reduction
of primitive adelic heights over a general number field.

## Provenance

The statement is derived. Springer, *Reduction theory over global fields*
(1994), §1.10, printed pp.210–211, PDF pp.4–5 (registered as
`springer-1994-reduction-global-fields`, SHA256
`774f5531200db07140b30ffb8f4adce8cf3a3914ca9f38b796f2a2d24ff18496`), bounds
the height of a rational vector of the form `λ e₁ + μ e₂` by choosing the
coefficients suitably. Over a general number field one cannot always take
`μ = 1` with a bounded integral correction, because the covering radius of the
integer lattice in the mixed space need not be small. The route implemented
here replaces that step by the classical simultaneous Dirichlet approximation
argument (pigeonhole principle on fractional parts of lattice coordinates),
applied to the image of the ring of integers in the mixed space. The theorem
is internal to this project's reduction route and is not quoted from a single
source statement.

## Definitions

* `Index F` is Mathlib's chosen index type of an integral basis of `𝓞 F`,
  `Module.Free.ChooseBasisIndex ℤ (𝓞 F)`.
* `basisBound F` is the real number
  `∑ i, ∑ w, normAtPlace w (latticeBasis F i)`: the sum over basis indices `i`
  and infinite places `w` of the place norms of Mathlib's `latticeBasis F i`,
  the image of the chosen integral basis in the mixed space. It bounds every
  place norm of every basis vector.

## Results

* `normAtPlace_sum_le`: the place norm of a finite sum in the mixed space is at
  most the sum of the place norms.
* `normAtPlace_combination_le`: if all real coefficients `c i` satisfy
  `|c i| ≤ ε` with `0 ≤ ε`, then `∑ i, c i • latticeBasis F i` has place norm at
  most `ε * basisBound F` at every infinite place.
* `exists_integer_eq_combination`: every integer combination of
  `latticeBasis F` is the mixed embedding of an algebraic integer.
* `card_index_pos`: the index type is nonempty, since its cardinality is the
  degree of `F` over `ℚ`.
* `exists_dirichlet`: for every point `z` of the mixed space and every positive
  natural number `N` there are algebraic integers `l` and `m` with `m ≠ 0` such
  that at every infinite place `w`,
  `normAtPlace w (mixedEmbedding F m) ≤ N * basisBound F` and
  `normAtPlace w (mixedEmbedding F l + mixedEmbedding F m * z) ≤ basisBound F / N`.
* `exists_dirichlet_infiniteAdeles`: the same statement for every element `y`
  of Mathlib's actual infinite adele ring `InfiniteAdeles F`, with the norms of
  the completions `‖algebraMap F (InfiniteAdeles F) m w‖` and
  `‖(algebraMap F (InfiniteAdeles F) l + algebraMap F (InfiniteAdeles F) m * y) w‖`.

## Proof

For each coefficient vector `a : Index F → Fin (N + 1)`, let `p a` be the
algebraic integer whose mixed embedding is `∑ i, a i • latticeBasis F i`, and
take the coordinates of `mixedEmbedding F (p a) * z` in the basis
`latticeBasis F`. Each fractional part of a coordinate lies in one of `N` cells
`[k/N, (k+1)/N)`, determined by `⌊N * fract⌋`. There are `(N + 1)^d`
coefficient vectors and only `N^d` cell patterns, `d` being the positive number
of basis indices, so the pigeonhole principle gives two distinct vectors `a` and
`a'` with the same pattern. Then all coordinate fractional parts differ by at
most `1/N`.

Take `m = p a - p a'`, realized as the integer combination with coefficients
`a i - a' i`, and `l` the integer combination with coefficients
`-(⌊coord a i⌋ - ⌊coord a' i⌋)`. The coefficients of `m` have absolute value at
most `N`, and `m ≠ 0` by linear independence of `latticeBasis F` because
`a ≠ a'`. The coordinates of `mixedEmbedding F l + mixedEmbedding F m * z` are
exactly the differences of the fractional parts, so they are bounded by `1/N`.
Both place-norm estimates follow from `normAtPlace_combination_le`.

The adelic version transports the point through Mathlib's ring equivalence
`InfiniteAdeleRing.ringEquiv_mixedSpace`, uses the published identification of
place norms `NormOneIdeleClass.normAtPlace_ringEquiv_mixedSpace`, and Mathlib's
compatibility of the mixed embedding with the algebra map into the infinite
adele ring.

## Scope

Only the infinite-place approximation is proved. The finite-place integrality
correction, the compact norm-one idele fundamental set, the rank-two height
bound, Iwasawa decompositions, the higher-rank induction and the general
reductive Siegel-cover theorem are not asserted here.
