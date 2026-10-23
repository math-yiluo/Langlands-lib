# Proof of the Cartan decomposition of `GL_m` over a discretely valued field

Author: Worker 305.

The closing theorem `Langlands.GeneralLinear.Cartan.cartanDecomposition` has
exactly `Langlands.GeneralLinear.CartanDecompositionStatement.{uF, uΓ}` as its
type, with both universes independent. It introduces the field `F`, the value
group `Γ₀`, the valuation `v`, the unit `ϖ` with
`Iwasawa.IsUniformizingElement v ϖ`, the rank `m` (zero included) and the
invertible matrix `g`. It adds no hypothesis and uses no axiom beyond
`propext`, `Classical.choice` and `Quot.sound`. The module imports only the
statement module `Langlands.Group.GL.CartanStatement`, which is unchanged.
It reuses the published Iwasawa API from
`Langlands.Representation.Whittaker.Iwasawa` (namespace
`Langlands.GeneralLinear.Iwasawa`).

The proof is elementary matrix algebra: Gaussian elimination with pivots of
largest valuation for existence, and bounds on minors for uniqueness. It does
not use Smith normal form, Cauchy–Binet or the Euclidean structure of
`v.integer`. Throughout, "integral" means having all entries in `v.integer`.
Membership in `Iwasawa.integralRange v m` is turned into integral entries by
`entry_mem_of_mem`.

## Integral factors do not increase entry and minor bounds

- `entry_mul_left_le` and `entry_mul_right_le`: suppose every entry of `A`
  has valuation at most `γ`. Then the same holds for `P * A` and for `A * Q`
  when `P` or `Q` is integral. Each entry of the product is a sum of products,
  and an integral factor has valuation at most one.
- `det_submatrix_mul`: for index maps `f h : Fin r → Fin m` (not necessarily
  injective), the minor `det ((P * B).submatrix f h)` equals the sum over all
  `φ : Fin r → Fin m` of `(∏ s, P (f s) (φ s)) * det (B.submatrix φ h)`. The
  proof expands each row of the minor as a linear combination of rows of `B`
  and applies multilinearity of `Matrix.detRowAlternating`.
- `minor_mul_left_le` and `minor_mul_right_le`: if every `r`-minor of `B` with
  arbitrary index maps has valuation at most `γ`, then so has every `r`-minor
  of `P * B` and of `B * Q` for integral `P` and `Q`. The left case follows from
  `det_submatrix_mul`, the ultrametric inequality, and `det_mem_integer` (the
  determinant of an integral matrix is integral). The right case follows by
  transposition.

## Uniqueness of the exponent

- `tailSum a k` is the sum of `a j` over the indices `j` with `k ≤ j`. Then
  `a i = tailSum a i - tailSum a (i + 1)` (`apply_eq_tailSum_sub`), so two
  exponent tuples with the same tail sums are equal (`eq_of_tailSum_eq`).
- `tailIndex m k : Fin (m - k) → Fin m` enumerates the indices `≥ k`
  increasingly. `sum_tailIndex` identifies its sum with `tailSum`.
- `tailSum_le_sum`: for antitone `b`, `tailSum b k` is at most the sum of `b`
  over any `m - k` distinct indices. The proof splits both index sets into their
  common part and their differences, which have equal sizes. Every index in the
  difference on the tail side is larger than every index in the other
  difference, so its `b`-value is smaller (`sum_le_sum_of_card_eq`).
- `minor_torus_le`: for antitone `b` and `v ϖ < 1`, every `(m - k)`-minor of
  `torus ϖ b` has valuation at most `v ϖ ^ tailSum b k`. If the row map is not
  injective, two rows coincide and the minor is zero. Otherwise the submatrix
  is `diagonal (ϖ ^ b ∘ f)` times an integral 0/1 matrix. The diagonal factor
  has valuation `v ϖ ^ ∑ b (f s)`, and `tailSum_le_sum` bounds it because
  `v ϖ < 1`.
- `tailSum_le_of_eq`: suppose `torus ϖ a = P * torus ϖ b * Q` with `P`, `Q`
  integral and `b` antitone. The minor of `torus ϖ a` on rows and columns
  `tailIndex m k` has valuation `v ϖ ^ tailSum a k`. By the two previous
  steps it is at most `v ϖ ^ tailSum b k`, hence
  `tailSum b k ≤ tailSum a k`.
- `exponent_unique`: from `k₁ * torus ϖ a * k₂ = k₁' * torus ϖ b * k₂'` with
  all four factors in `integralRange v m` and `a`, `b` antitone,
  `torus ϖ a = (k₁⁻¹ * k₁') * torus ϖ b * (k₂' * k₂⁻¹)` and symmetrically.
  Both outer factors are integral because `integralRange v m` is a subgroup.
  Applying `tailSum_le_of_eq` both ways gives equal tail sums, hence `a = b`.

## Existence of the decomposition

The theorem `exists_cartan` proves existence for every rank by structural
recursion on `m`. In rank zero the exponent is the empty function and both
integral factors are `1`. In rank `m + 1` the steps are:

1. **Pivot** (`exists_pivot`). Choose an entry `g x.1 x.2` of maximal
   valuation. Permutation matrices `permGL` of the transpositions exchanging
   `x.1` and `x.2` with the last index move it to the last diagonal place.
   `permGL` is built with `Iwasawa.ofInverse` from `permMat σ` and
   `permMat σ.symm`. Its entries are 0 or 1, so it lies in
   `integralSubgroup v.integer m` (`permGL_mem`). The pivot is nonzero:
   otherwise every entry of `g` would have valuation zero, so the last row of
   `g` would vanish, contradicting invertibility. In `g1 = p₁ * g * p₂` every entry has valuation at most
   that of the last diagonal entry `p`.
2. **Clear the last row.** The published `Iwasawa.exists_clear_last_row` gives
   an integral `c₁` such that the last row of `g1 * c₁` is `(0, …, 0, p)`. By
   `entry_mul_right_le`, `p` still dominates all entries.
3. **Clear the last column** (`exists_clear_last_col`). With
   `c i = h i last / p` (integral by dominance) and
   `N = (Iwasawa.lastRowClearing c)ᵀ`, we have `N * N = 0`. So `1 - N` is
   integral with integral inverse `1 + N`; call this invertible matrix `k`.
   Left multiplication by it subtracts
   `c i` times the last row from row `i`. This clears the last column above
   the pivot and leaves the last row unchanged. The result `h3` has last row
   and last column zero except for `p` at the corner, and `p` still dominates
   all entries (`entry_mul_left_le`). Here `h3 = k * (g1 * c₁)`.
4. **Recurse.** `Iwasawa.det_eq_last_mul_det_castSucc` gives
   `det h3 = p * det A`, where `A` is the upper-left `m × m` block. So `A` is
   invertible (`GeneralLinearGroup.mkOfDetNeZero`). The recursive call gives an
   antitone `mu` and integral `k₁`, `k₂` with `A = k₁ * torus ϖ mu * k₂`.
5. **The last exponent is smallest.** The uniformizer condition gives
   `v p = v ϖ ^ e`, and `ε = p * ϖ ^ (-e)` is a unit of valuation one. Since
   `torus ϖ mu = k₁⁻¹ * A * k₂⁻¹` and all entries of `A` have valuation at most
   `v p`, each diagonal entry satisfies `v ϖ ^ mu i ≤ v ϖ ^ e`. Since
   `v ϖ < 1`, this gives `e ≤ mu i`. Hence `Fin.snoc mu e` is antitone
   (`antitone_snoc`).
6. **Reassemble.** Let `ι = Iwasawa.rankInclusion 1` (block-diagonal embedding
   with a `1` in the last place), and let `D x` be the `diagonalUnits` with
   entries `1, …, 1, x`. The following identities are checked entrywise by
   cases on `Fin.lastCases`:
   `h3 = ι A * D p` (`hI1`); `ι k₂ * D p = D (ϖ ^ e) * (ι k₂ * D ε)` (`hI2`);
   and `ι (torus ϖ mu) * D (ϖ ^ e) = torus ϖ (Fin.snoc mu e)` (`hI3`).
   Since `g = p₁⁻¹ * k⁻¹ * h3 * c₁⁻¹ * p₂⁻¹`, we get
   `g = (p₁⁻¹ * k⁻¹ * ι k₁) * torus ϖ (Fin.snoc mu e) * (ι k₂ * D ε * c₁⁻¹ * p₂⁻¹)`.
   Both outer factors lie in `integralRange v (m + 1)`, which is
   `integralSubgroup v.integer m` by `Iwasawa.integralRange_succ`. The proof
   uses `Iwasawa.rankInclusion_mem` and `Iwasawa.diagonalUnits_mem` for the
   unit-valuation diagonal `D ε`.

## The closing theorem

`cartanDecomposition` takes the existence witness from `exists_cartan`.
Given any other antitone exponent `mu` with a decomposition of the same `g`,
it applies `exponent_unique` to the equality of the two factorizations.

## Provenance

This is a proof artifact. The target statement and its literature provenance
(Gross, *On the Satake isomorphism*, Proposition 2.6) are documented in
[CartanStatement.md](CartanStatement.md). Both halves above are standard
elementary-divisor arguments, written directly for this formalization. Every
other declaration in this module is an internal auxiliary lemma for this proof.
