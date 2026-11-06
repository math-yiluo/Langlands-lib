# Proof that power maps have non-open image on number-field adelic units

Author: Worker 105.

`numberFieldPowerImage` proves `NumberFieldPowerImageStatement`: for every number
field `K` and every `n ≥ 2`, the image of `x ↦ x ^ n` is not open in `(Adeles K)ˣ`,
and the image of the actual power morphism is not open on punctured-line points.
Brian Conrad, *Weil and Grothendieck approaches to adelic points* (December 31,
2011), printed p.11, asserts the result without an argument. The registered
source is `conrad-2011-weil-grothendieck-adelic-points`, SHA-256
`fe4a9193aff4ef575665b40971f3da32f850a74d87b3f2d0fa28bba26b9cbabb`.
This proof is an independent derivation of that assertion: infinitely many places
have local units that are not `n`th powers, and placing these units at distinct
places produces a sequence tending to `1` outside the power image.

## Residue fields

`exists_not_pow_mod`: let `P` be a maximal ideal of a commutative ring `B` with
finite quotient, and let `ℓ` be a prime dividing `n ≠ 0` and `|B/P| - 1`. Then some
`c : B` has `a ^ n - c ∉ P` for every `a : B`. The proof uses that the unit group
of the finite field `B/P` has `|B/P| - 1` elements (`Nat.card_units`). By Cauchy's
theorem (`exists_prime_orderOf_dvd_card'`) it has an element of order `ℓ`, so
`x ↦ x ^ ℓ` is not injective on it. A self-map of a finite set is injective exactly
when it is surjective, so some unit `g` is not an `ℓ`th power. A lift `c` of `g`
works: if `a ^ n ≡ c`, then the residue of `a` is a unit and `g` is the `ℓ`th power
of its `(n / ℓ)`th power.

## Completions

`not_pow_in_adicCompletion` works for any Dedekind domain `B` with fraction field
`K` and any height-one prime `w`. If `c : B` satisfies `a ^ n - c ∉ w` for all `a`,
then the image of `c` in the completion `w.adicCompletion K` is not an `n`th power.
Suppose `z ^ n = c`. Since `c ∉ w`, `c` has valuation `1`, so `z` has valuation `1`
(`pow_eq_one_iff_of_nonneg`). Choose a uniformizer `π`. The set of `y` with
`(z - y) / π` integral is open (`Valued.isOpen_integer`), so density of `K`
(`HeightOneSpectrum.denseRange_algebraMap`) gives `x ∈ K` with `v(z - x) < 1`. Then
`v(x) ≤ 1`, and Mathlib's `exists_valuation_sub_lt_of_integer` gives `a : B` with
`v(a - x) < 1`. So `v(z - a) < 1`. Factor `z ^ n - a ^ n` as `(z - a)` times a
geometric sum of integral terms (`geom_sum₂_mul`); its valuation is below `1`. Hence
`c - a ^ n` has valuation below `1`, so it lies in `w`
(`intValuation_lt_one_iff_mem`), a contradiction.

## Infinitely many good places

`exists_place_card_modEq_one`: for a prime `ℓ` and any `N`, Mathlib's
`Nat.exists_prime_gt_modEq_one` gives a prime `p > N` with `p ≡ 1 (mod ℓ)`. Going-up
(`exists_ideal_over_prime_of_isIntegral_of_isDomain`) gives a finite place `v` of `K`
over `p`. Its residue field has `p ^ f` elements, with `f = v.inertiaDeg ℤ`
(`Ideal.natAbs_pow_inertiaDeg`) and `f ≠ 0` because the quotient is nontrivial. So
the cardinality exceeds `N` and is `≡ 1 (mod ℓ)`.
`infinite_places_card_modEq_one` concludes that the places with residue cardinality
`≡ 1 (mod ℓ)` form an infinite set, since their cardinalities are unbounded.

## Assembly

`not_isOpen_range_pow_of_tendsto`: in a topological monoid, if a sequence tending to
`1` avoids the image of `x ↦ x ^ n`, the image is not open, since it contains `1`.
`units_tendsto_one` reduces convergence of units to convergence of their values and
inverse values (`Units.isEmbedding_embedProduct`).

In `numberField_units_powerImage_not_open`, choose a prime `ℓ ∣ n`
(`Nat.exists_prime_and_dvd`), an injective sequence `e` of good places, and for each
good place the element `c_v` from `exists_not_pow_mod`. Let `a_v` be the image of
`c_v` in the completed valuation ring at good places and `1` elsewhere. Every `a_v` is
a unit of the valuation ring. The published `restrictedUnitAtPlace` puts `a_v` at the
single place `e m` and `1` elsewhere, and keeps every archimedean coordinate `1`.
These units tend to `1`, by the published `tendsto_restrictedUnitAtPlace_val`. Their
inverses are the one-place units of the inverse values
(`restrictedUnitAtPlace_inv_val`), which also tend to `1`. If the `m`th unit were
`y ^ n`, its coordinate at `e m` would be an `n`th power in the completion
(`RestrictedProduct.pow_apply`), contradicting `not_pow_in_adicCompletion`.

## Punctured-line points

`schemePoints_powerImage_not_open` uses the published homeomorphism
`affineLinePunctureUnitHomeomorph R S` from actual punctured-line points to units, for
any base ring `R`. By `affineLinePunctureUnitHomeomorph_pow`, it carries composition
with `affineLinePuncturePow R n` to the `n`th-power map. So the image of the power
morphism pulls back under the inverse homeomorphism to the unit power image.
If the scheme-point image were open, its pullback would be open, a contradiction.
`numberFieldPowerImage` combines the two clauses, in arbitrary universe `u`,
for the full adele ring and every base ring `R` in the published statement.
