# Proof of the real local Tate theory

This module proves the published Library proposition
`Langlands.LocalFactor.RealArchimedeanTateStatement` (Library file
`Langlands/LocalFactor/Archimedean/Statement.lean`, conventions in its paired Markdown)
as the theorem

`Langlands.LocalFactor.RealTate.realArchimedeanTateStatement : RealArchimedeanTateStatement`.

It adds no hypotheses and no axioms; the axiom closure is `propext`, `Classical.choice`,
`Quot.sound`. It uses the helper modules `RealTateZeta` (zeta integrals, convergence,
holomorphy, dilation), `RealTateGaussian` (Schwartz Gaussians) and `RealTateIdentity`
(Tate's identity), and the published Library Gaussian computations of
`Langlands.Global.Hecke` (`realGaussian`, `integral_realGaussian_mul_fourierChar`,
`integral_realGaussian_mul_realCharFun`).

## The four conjuncts

The statement's local `integrand f e t s` is `integrand f e (s + t)` of `RealTateZeta`
definitionally, and its `zeta f e t s` is `zeta f e (s + t)`; its `ft a c f` is the
dilated, scaled inverse Fourier transform `y ↦ c ∫ exp(2π i a x y) f(x) dx`.

1. **Convergence** (`0 < Re(s + t)` gives integrability): `integrable_integrand`.
2. **Unique continuation**: the function `contZetaNF f e t` satisfies the extension
   property (`contZetaNF_spec`), and any two functions with the property are equal
   (`extension_unique`).
3. **Functional equation**: the witness is `g = dilatedFourierInv f a c`, which is the
   Schwartz function `y ↦ c (𝓕⁻ f)(a y)` and agrees with `ft a c f` (`dilatedFourierInv_eq`);
   the germ identity is `functional_equation`. The hypothesis `0 < c` is not needed.
4. **Gaussian normalization**: the Schwartz Gaussian is `gaussSchwartzE e`
   (`gaussSchwartzE_apply`); the Fourier eigenvalue identity
   `ft 1 1 (gaussian e) = i^e gaussian e` is `integral_exp_mul_gaussian`; the Gaussian
   zeta integral `Γℝ(s + t + e)` is `zeta_gaussian`.

## Implemented proof

**Identity theorem.** `eventuallyEq_nhdsNE_of_eqOn`: two functions meromorphic on `ℂ`
that agree on a nonempty open set agree on a punctured neighbourhood of every point,
because the meromorphic order of their difference is `⊤` at one point and hence everywhere
(`MeromorphicOn.meromorphicOrderAt_eq_top_of_isPreconnected`, `ℂ` being connected).
`eq_of_meromorphicNFOn`: in meromorphic normal form they are then equal everywhere
(`MeromorphicNFAt.eventuallyEq_nhdsNE_iff_eventuallyEq_nhds`). `meromorphicAt_Gammaℝ`:
`Γℝ` is meromorphic everywhere, as the inverse of the entire function `1/Γℝ`.

**Gaussian facts.** `gaussian e x = x^e exp(-π x²)` equals the Library's
`realGaussian 1 e x`. `integral_exp_mul_gaussian` (Fourier eigenfunction:
`∫ exp(2π i x y) x^e e^{-πx²} dx = i^e y^e e^{-πy²}`) is the Library lemma
`integral_realGaussian_mul_fourierChar` at `a = 1`, and `zeta_gaussian`
(`Z(gaussian e, e, w) = Γℝ(w + e)` for `0 < Re w`) is the Library lemma
`integral_realGaussian_mul_realCharFun`. Consequently (`zeta_gaussSchwartzE`,
`fourierInv_gaussSchwartzE`, `zeta_fourierInv_gaussSchwartzE`) the Schwartz Gaussian `G`
satisfies `Z(G, e, w) = Γℝ(w + e)` and `Z(𝓕⁻ G, e, w) = i^e Γℝ(w + e)` for `0 < Re w`.

**Functional equation on the strip.** `zeta_fourierInv_mul_Gammaℝ`: for `0 < Re u < 1`,
`Z(𝓕⁻ f, e, 1 - u) Γℝ(u + e) = i^e Γℝ(1 - u + e) Z(f, e, u)`. This is Tate's identity
(`tate_identity`) with `h = G`, followed by the two Gaussian zeta evaluations.

**Continuation.** `contFormula f e u = Z(𝓕⁻ f, e, 1 - u) Γℝ(u + e) / (i^e Γℝ(1 - u + e))`
is meromorphic on `Re u < 1` (`meromorphicAt_contFormula`: `Z(𝓕⁻ f, e, ·)` is analytic on
`Re > 0` by `analyticAt_zeta`, and `Γℝ` is meromorphic), and equals `Z(f, e, u)` on the
strip (`zeta_eq_contFormula`, using `Γℝ ≠ 0` for positive real part). The glued function
`contZeta f e u` (`Z(f, e, u)` if `0 < Re u`, `contFormula f e u` otherwise) is therefore
meromorphic at every point (`meromorphicAt_contZeta`; near points with `Re u ≤ 0` it agrees
with `contFormula` because the two pieces agree on the overlap). The continuation
`contZetaNF f e t` is Mathlib's normal form `toMeromorphicNFOn` of `s ↦ contZeta f e (s + t)`
on `ℂ`. `contZetaNF_spec`: it is in normal form, and at `s` with `0 < Re(s + t)` the glued
function is analytic, so the normal form does not change its value
(`toMeromorphicNFOn_eq_toMeromorphicNFAt`, `toMeromorphicNFAt_eq_self`).
`extension_unique` is the identity theorem on the open half-plane `0 < Re(s + t)`.

**Dilation.** `dilatedFourierInv f a c = c • (𝓕⁻ f ∘ (a ·))`, built with
`SchwartzMap.compCLMOfContinuousLinearEquiv` and `ContinuousLinearEquiv.unitsEquivAut`.
`zeta_dilatedFourierInv`: `Z(c (𝓕⁻ f)(a ·), e, w) = c sgn(a)^e |a|^(-w) Z(𝓕⁻ f, e, w)` for
all `w`, from the dilation lemma `zeta_eq_sign_mul_zeta_comp_mul` and
`sgn(a)^e sgn(a)^e = 1`.

**Germ identity.** `functional_equation`: given `Z` extending `Z(f, e, · + t)` and `Y`
extending `Z(g, e, · - t)` (both in normal form), the two sides
`s ↦ Y(1 - s) / Γℝ(1 - s - t + e)` and
`s ↦ c sgn(a)^e |a|^(s + t - 1) i^e Z(s) / Γℝ(s + t + e)` are meromorphic on `ℂ`. On the open
strip `0 < Re(s + t) < 1` (nonempty: it contains `1/2 - t`) they are equal: there
`Y(1 - s) = Z(g, e, 1 - (s + t))` and `Z(s) = Z(f, e, s + t)`, the dilation lemma rewrites
the first as `c sgn(a)^e |a|^(s + t - 1) Z(𝓕⁻ f, e, 1 - (s + t))`, and the strip
functional equation with `u = s + t` finishes the computation (`field_simp`, with the
Gamma values nonzero). The identity theorem then gives equality on a punctured
neighbourhood of every `s₀`.

## Provenance

Tate's local functional equation at the real place: J. T. Tate, *Fourier analysis in
number fields and Hecke's zeta-functions* (Cassels–Fröhlich 1967, Chapter XV),
section 2.4 (Lemma 2.4.1, Theorem 2.4.1) and section 2.5 (the real computation with
`x^e exp(-π x²)`); scaling of the additive character and Haar measure as in Tate,
*Number theoretic background* (Corvallis 1979), (3.2.1)–(3.2.5). The Library statement's
Markdown records these sources. The implementation route (meromorphic continuation of the
strip identity by gluing and normal form, rather than Tate's explicit computation of
`ρ(c)`) is the one described above.
