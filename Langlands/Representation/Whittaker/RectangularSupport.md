# Support of spherical Whittaker functions on rectangular lower blocks

Module `Langlands.Representation.Whittaker.RectangularSupport`, namespace
`Langlands.GeneralLinear.RectangularSupport`.

## Content

Fix `t < r`. For a commutative ring `R`, `g ∈ GL_(t+1)(R)` and an
`(r-t-1) × (t+1)` matrix `x` over `R`, `rectGL h g x ∈ GL_(r+1)(R)` is the block matrix

```text
[[g, 0, 0],
 [x, I, 0],
 [0, 0, 1]]
```

(blocks of sizes `t+1`, `r-t-1`, `1`). It uses the same expression as the Library's adelic
`rectangularPoint` (module `Langlands.Global.RankinSelberg.WhittakerIntegrals`). Over
`R = 𝔸`, the matrix of `rectangularPoint F h g x` is `rectGL h (E g) x`, where `E` is the
matrix of the adelic point `g`.

### Matrix identities over a commutative ring

- `rectGL_apply`: the entries of `rectGL h g x`, as an explicit case split on the row and
  column indices.
- `rectGL_mul`: `rectGL h P z * rectGL h Q w = rectGL h (P Q) (z Q + w)`.
- `rectGL_one_zero`: `rectGL h 1 0 = 1`.
- `rectGL_zero`: `rectGL h Q 0` is the Library's padding `padGL _ Q = diag(Q, I)`.

### Over a valued field

`F` is a field with a valuation `v`, `𝒪 = v.integer`, and `GL_(n+1)(𝒪)` is the Library's
`Langlands.Conductor.integralSubgroup v.integer n` (entries of `k` and `k⁻¹` in `𝒪`).

- `rectGL_mem_integralSubgroup`: if `k ∈ GL_(t+1)(𝒪)` and all entries of `z` lie in `𝒪`,
  then `rectGL h k z ∈ GL_(r+1)(𝒪)`. `rectGL_zero_mem_integralSubgroup` is the case
  `z = 0`.
- `eq_zero_of_basisRow` (the character trick). Let `θ` be a character of the upper
  unitriangular group `N_(n+1)(F)` with `θ(u) = χ(∑_i u_(i,i+1))` for a function
  `χ : F → ℂ`. Assume `χ(c z) ≠ 1` for some `c ∈ 𝒪` whenever `z ∉ 𝒪`. Let
  `f : GL_(n+1)(F) → ℂ` satisfy `f(u g) = θ(u) f(g)` for `u ∈ N_(n+1)(F)`, and
  `f(g k) = f(g)` for `k ∈ GL_(n+1)(𝒪)`. Let `g` be a matrix whose row `p+1` is the
  standard basis row `e_(p+1)`, whose column `c₀` vanishes from row `p+1` down, and whose
  entry `g_(p,c₀)` is not in `𝒪`. Then `f(g) = 0`.
- `apply_rectGL` (support lemma). Under the same hypotheses on `θ`, `χ`, `f` with `n = r`:
  `f(rectGL h Q z) = f(rectGL h Q 0)` if every entry of `z` lies in `𝒪`, and
  `f(rectGL h Q z) = 0` otherwise. This holds for every `Q ∈ GL_(t+1)(F)`.
- `apply_rectGL_zero_mul`. If moreover `f(1) = 1`, `k ∈ GL_(t+1)(𝒪)` and
  `w ∈ GL_(r+1)(𝒪)`, then for every `x`
  `f(diag(P, I) · rectGL h k x · w) = f(diag(P, I)) · f(rectGL h k x · w)`.
  Both sides vanish unless `x` is integral, and otherwise both equal `f(diag(P, I))`.

### Spherical Whittaker functions

Here `F` also carries a topology, `ψ` is a unitary additive character of `F` with `ψ = 1`
on `𝒪` and with `ψ(c z) ≠ 1` for some `c ∈ 𝒪` whenever `z ∉ 𝒪` (that is, `ψ` has
conductor exactly `𝒪`). `ϖ` is uniformizing for `v`, `q ∈ ℕ` and `a : Fin (r+1) → ℂˣ`.
`W°` denotes the Library's explicit spherical Whittaker function
`Langlands.GeneralLinear.Spherical.sphericalWhittaker hϖ θ q a`, and the characters are the
Library's `Whittaker.standardCharacter ψ r` (`u ↦ ψ(∑ u_(i,i+1))`) and
`Whittaker.inverseStandardCharacter ψ r` (its pointwise inverse).

- `sphericalWhittaker_standard_rectGL`, `sphericalWhittaker_inverseStandard_rectGL`:
  `apply_rectGL` for `W°` with the standard and with the inverse standard character.
- `sphericalWhittaker_inverseStandard_rectGL_zero_mul`: `apply_rectGL_zero_mul` for `W°`
  with the inverse standard character.

The hypotheses on `f` are discharged by the Library lemmas `sphericalWhittaker_mem`
(left `θ`-equivariance), `sphericalWhittaker_mul_integral` (right
`GL_(r+1)(𝒪)`-invariance) and `sphericalWhittaker_one` (`W°(1) = 1`), with
`isIntegrallyTrivial_standardCharacter` and `isIntegrallyTrivial_inverseStandardCharacter`.

## Proofs

`rectGL_apply`, `rectGL_zero` and `rectGL_one_zero` compute entries through the reindexing
`Fin ((t+1) + (r-t)) ≃ Fin (r+1)` and the block decomposition. `rectGL_mul` is the
Library's `lowerBlockPair_mul_lowerBlockPair`.

`rectGL_mem_integralSubgroup` checks the entries of `rectGL h k z` and of its inverse
`rectGL h k⁻¹ (-(z k⁻¹))`.

`eq_zero_of_basisRow`: choose `c ∈ 𝒪` with `χ(c g_(p,c₀)) ≠ 1`. The transvection
`k = I + c E_(c₀,p+1)` lies in `GL_(n+1)(𝒪)`. Since row `p+1` of `g` is `e_(p+1)`,
`g k = n g`, where `n = I + E` and `E` has column `p+1` equal to `c` times column `c₀`
of `g` and is zero elsewhere. As column `c₀` of `g` vanishes from row `p+1` down, `n` is
upper unitriangular, `E² = 0`, and the only superdiagonal entry of `E` is
`n_(p,p+1) = c g_(p,c₀)`. Hence `f(g) = f(g k) = f(n g) = χ(c g_(p,c₀)) f(g)`, so
`f(g) = 0`.

`apply_rectGL`: for integral `z₂`, `rectGL h Q (z₁ + z₂) = rectGL h Q z₁ · rectGL h 1 z₂`,
and the second factor lies in `GL_(r+1)(𝒪)`. This settles the integral case with
`z₁ = 0`. Otherwise let `i₀` be the largest row of `z` with a non-integral entry, say in
column `j₀`. Write `z = z₁ + z₂`, where `z₁` keeps the rows `≤ i₀` and `z₂` the rows
`> i₀`. Then `z₂` is integral, so `f(rectGL h Q z) = f(rectGL h Q z₁)`. Use 0-based
indices, so that row `t+1+i` of `rectGL h Q z₁` begins with row `i` of `z₁`. Then row
`t+2+i₀` is a standard basis row, column `j₀` vanishes from row `t+2+i₀` down, and the
entry in row `t+1+i₀`, column `j₀` is `z_(i₀,j₀) ∉ 𝒪`. The character trick with
`p = t+1+i₀` and `c₀ = j₀` then gives `0`.

`apply_rectGL_zero_mul`: `rectGL h P 0 · rectGL h k x = rectGL h (P k) x` by
`rectGL_mul`. Right invariance removes `w`, and `apply_rectGL` reduces both sides to
`[x integral] · f(rectGL h (P k) 0)` and `[x integral] · f(rectGL h P 0) · f(rectGL h k 0)`.
Finally `rectGL h (P k) 0 = rectGL h P 0 · rectGL h k 0`, with `rectGL h k 0` integral, and
`f(rectGL h k 0) = f(1) = 1`.

## Provenance

Internal. These are elementary lemmas written for the direct computation of the unramified
dual Rankin–Selberg integral at a place `v ∉ S`. That computation is part of the proof of
`Langlands.Global.RankinSelbergGlobal.UnequalDualEulerFactorizationStatement` (J. W.
Cogdell, *Analytic theory of L-functions for GL_n*, 2004, `cogdell-2004-analytic-theory-gln`,
printed p.220). In the unramified dual integral the inner integral over `x` collapses to
the integral `x`. The support lemma above proves that collapse. Cogdell obtains the
unramified dual factor from the local functional equation (p.220 with Theorems 3.2–3.3,
pp.214–215) rather than by this computation. The character trick is the standard argument
that a `θ`-equivariant, right `GL(𝒪)`-invariant function vanishes when `θ` is nontrivial
on the relevant conjugate of `GL(𝒪)`.
