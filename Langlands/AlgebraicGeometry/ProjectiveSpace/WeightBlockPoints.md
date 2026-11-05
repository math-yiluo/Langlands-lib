# Weight-block rational points of closed sets stable under a diagonal scaling

This is a helper module for the proof of
`Langlands.GroupScheme.ProjectiveTorusFixedPointDimensionStatement`, which is
Milne's *Algebraic Groups* (2017), Proposition 20.11, printed pp. 410–411
(PDF pp. 426–427). It proves the core of that proposition for a single
cocharacter acting diagonally on `ProjectiveSpace K n = Proj K[X_0, …, X_n]`.
The proposition is stated with homogeneous coordinates (`HasCoordinates`, from
`RationalPointZeros`) and Mathlib's `topologicalKrullDim`. The group-scheme
statement is not used here.

## Main result

`exists_weightBlock_points`. Let `K` be algebraically closed, and let `Z` be a
closed subset of projective `n`-space over `K`. Let `m : Fin (n + 1) → ℤ` be
integer weights. Suppose `Z` is stable under the diagonal scaling: for every
unit `z`, every point `x ∈ Z` with coordinates `c`, and every point `y` with
coordinates `(z ^ m i * c i)_i`, we have `y ∈ Z`. Let `d` be a natural number
with `d ≤ topologicalKrullDim Z`. Then there are vectors
`c 0, …, c d : Fin (n + 1) → K` such that

- each `c j` is nonzero;
- every point with coordinates `c j` lies in `Z`;
- each `c j` is supported on one weight block: if `c j i ≠ 0` and `c j l ≠ 0`,
  then `m i = m l`;
- for `j ≠ j'` and every scalar `a`, `c j' ≠ a • c j`, so the `c j` are pairwise
  non-proportional.

The proposition does not assume that `Z` is irreducible or that it has finitely
many weight-block points.

## Proof as implemented

Let `J` be the homogeneous vanishing ideal of `Z` in `K[X_0, …, X_n]`, and let
`M` be the irrelevant ideal `(X_0, …, X_n)`.

1. *Ordering.* Sort the coordinates by weight. `σ := Tuple.sort m` satisfies
   `Monotone (m ∘ σ)`. Put `x i := X (σ i)`.
2. *Greedy set.* Let `A` be the set of indices `i` such that `x i` is not in
   the radical of `J + (x j : j < i)`. Then `mem_radical_sup_span_greedy` shows
   that every `x i`, and hence `M`, lies in the radical of `J + (x i : i ∈ A)`.
3. *Upper bound.* `height_map_mk_le_card` is Krull's height theorem
   (`Ideal.height_le_card_of_mem_minimalPrimes_span_finset`) in `K[X] ⧸ J`.
   It gives `height (M / J) ≤ |A|`, because `M / J` is a minimal prime over the
   images of the `x i`, `i ∈ A`.
4. *Lower bound.* `le_height_map_irrelevantIdeal` shows `J ≤ M` and
   `d + 1 ≤ height (M / J)`. A chain `t_0 < … < t_d` of irreducible closed
   subsets of `Z` has generic points, whose homogeneous primes contain `J` and
   form a strictly decreasing chain (`ProjectiveSpectrum.le_iff_mem_closure`
   gives inclusion; distinct closures give strictness). Each of these primes
   is strictly inside `M` (`asHomogeneousIdeal_lt_irrelevantIdeal`). Their
   images in `K[X] ⧸ J` therefore form a chain of length `d + 1` ending at
   `M / J`. Then `Order.length_le_height_last` and
   `PrimeSpectrum.height_eq_orderHeight` give the bound. Steps 3 and 4 give
   `d + 1 ≤ |A|`.
5. *Points.* For `i ∈ A`, the Nullstellensatz
   (`MvPolynomial.vanishingIdeal_zeroLocus_eq_radical`) gives a vector `v`. It
   annihilates `J`, has `v (σ j) = 0` for `j < i`, and has `v (σ i) ≠ 0`. Choose
   `d + 1` distinct indices `e 0, …, e d` of `A` with `Finset.orderEmbOfFin`.
   Let `c j` be the weight-`m (σ (e j))` part of the corresponding `v j`
   (`FlagCore.weightPart`).
6. *Membership.* The vector `v j` is the coordinate vector of a point of `Z`
   (`exists_hasCoordinates`, `mem_of_eval_eq_zero`). By the stability hypothesis,
   every scaled vector `(z ^ m i * v j i)_i` also has a point in `Z`, so every
   homogeneous element of `J` vanishes there (`eval_eq_zero_of_mem`). All nonzero
   coordinates of `v j` have weight at least `m (σ (e j))`, because the weights
   are sorted and the earlier coordinates vanish. The lowest-weight limit lemma
   `FlagCore.eval_weightPart_eq_zero` then shows that the homogeneous elements
   of `J` vanish at `c j`, so every point with coordinates `c j` lies in `Z`.
   This is the limit `lim_{t → 0} t[v]` of Milne's proof (his reference 13.17).
7. *Non-proportionality.* Each `c j` is nonzero at `σ (e j)` and zero at
   `σ (e j'')` for every `e j'' < e j`. Two such vectors with `e j ≠ e j'` cannot
   be proportional.

## Helper declarations

- `mem_radical_sup_span_greedy`: the greedy radical generation of step 2, by
  well-founded induction on `Fin N`.
- `comap_map_mk_of_le`, `map_mk_lt_map_mk`: ideals containing `J` are recovered
  from their images in `R ⧸ J`, and strict inclusions are preserved.
- `height_map_mk_le_card`: Krull's height theorem modulo `J` (step 3).
- `exists_hasCoordinates`: every nonzero vector is the coordinate vector of a
  rational point, via `hasCoordinates_fromOfGlobalSections`.
- `vanishingIdealOf`, `mem_vanishingIdealOf`: the vanishing ideal of a set, as
  an ideal of the coordinate ring (an abbreviation for the underlying ideal of
  `ProjectiveSpectrum.vanishingIdeal`).
- `homogeneousComponent_mem_vanishingIdealOf`: the vanishing ideal is homogeneous.
- `eval_eq_zero_of_mem`, `mem_of_eval_eq_zero`: a point of `Z` with coordinates
  `c` annihilates the homogeneous elements of `J`; conversely, for closed `Z`,
  a point whose coordinates annihilate them lies in `Z`.
- `irrelevantIdeal` (an abbreviation), `mem_irrelevantIdeal_iff`,
  `X_mem_irrelevantIdeal`, `irrelevantIdeal_isMaximal`: the irrelevant ideal is
  the kernel of the constant coefficient, so it is maximal.
- `asHomogeneousIdeal_lt_irrelevantIdeal`: the prime of every point of
  projective space is strictly inside the irrelevant ideal.
- `le_height_map_irrelevantIdeal`: the lower bound of step 4.

## Relation to the source

Milne reduces to `G_m` acting with weights `m_i` on an eigenvector basis, and
to irreducible `X`. He argues by induction on `dim X` with hyperplane sections
`X ∩ P(W)` (Lemma 20.10), and takes one more fixed point as a limit
`lim_{t → 0} t[v]`. The route above is different and was chosen for this
formalization. It works on the affine cone and replaces the hyperplane induction
by one application of Krull's height theorem to the greedy set of coordinates.
It needs neither irreducibility nor Lemma 20.10's nonemptiness of `X ∩ H`. The
lowest-weight limit of step 6 is the same device as Milne's final limit.
Reducing the group-scheme proposition to this coordinate statement is done in
the proof module.
