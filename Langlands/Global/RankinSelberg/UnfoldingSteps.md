# Generic unfolding steps over `N_m(F) \ GL_m(𝔸)`

Internal helper module for `UnequalUnfoldingReduction.md`. It packages
the three measure-theoretic steps shared by the ordinary and the dual
unfolding, for arbitrary functions on `GL_m(𝔸)` (`m = t + 1`).
Provenance: internal.

## Groups and cosets

- `isInvInvariant_of_isMulRightInvariant`: a regular Haar measure that
  is also right invariant is invariant under inversion (applied to
  `N_m(𝔸)`, whose Haar measure is right invariant by the Library's
  compact-quotient theorem).
- `existsUnique_of_image`: a strict fundamental domain for the image of
  `Λ ≤ N` in `H` is one for `Λ` acting through `N`.
- `RationalCosetIndex`, `rationalCosetRep`: the index set
  `N_m(F) \ GL_m(F)` (right cosets inside the rational subgroup of
  `GL_m(𝔸)`) and chosen representatives; countable.
- `mem_unipotentRationalImage_iff`: `N_m(F) ⊂ GL_m(𝔸)` is the image of
  the rational subgroup of `N_m(𝔸)`.
- `cosetRightMul`, `rationalCosetRep_mul`: right translation by
  `GL_m(F)` permutes the cosets, and representatives move up to
  `N_m(F)`.

## Step 1: unfolding an orbit sum (`OrbitSum`)

For `f` measurable and left `N_m(F)`-invariant and `I` with
`HasSum (q ↦ f(ρ(q) x)) (I x)` for every `x`:
`rational_mul_of_hasSum` (then `I` is left `GL_m(F)`-invariant),
`measurable_of_hasSum`, and `integral_rationalQuotient_eq_of_hasSum`:
if `f` is integrable on the chosen fundamental domain of `N_m(F)`, then
`∫_{GL_m(F) \ GL_m(𝔸)} I(q.out) = ∫_{fd(N_m(F))} f` for the Library's
`rationalQuotientHaarMeasure`.

## Step 2: averaging over `N_m(F) \ N_m(𝔸)` (`Average`)

`unipotentFundamentalDomain` is the chosen fundamental domain of
`N_m(F)` in `N_m(𝔸)`. `haar_unipotentFundamentalDomain`,
`quotientMassNormalizer_mul_haar`: its Haar mass is the inverse of the
Library's `quotientMassNormalizer`.
`integrableOn_and_setIntegral_average` and `setIntegral_eq_of_average`:
if `∫_{n ∈ fd} f(n x) dn = mass • g(x)` for all `x`, then `g` is
integrable on the fundamental domain of `N_m(F)` in `GL_m(𝔸)` and has
the same integral as `f` there.

## Step 3: the Whittaker quotient (`WhittakerSide`)

`integrable_and_integral_whittakerQuotient`: for `g` measurable, left
`N_m(𝔸)`-invariant and integrable on the fundamental domain of
`N_m(F)`, the function `q ↦ g(q.out)` on `N_m(𝔸) \ GL_m(𝔸)` is
integrable for `whittakerQuotientMeasure` with the same integral.
