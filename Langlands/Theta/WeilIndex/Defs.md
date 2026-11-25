# The Weil index

**GKT §3.1**: 3.1.3 (characters of second degree, (3.6), Remark 3.1, p. 71), **Theorem 3.3**
(p. 73), **Definition 3.4** and **Corollary 3.6** (p. 76), **Proposition 3.10** (p. 79),
**Corollaries 3.11, 3.12** (p. 80); from §3.2, **Proposition 3.13 (a), (d)** (p. 81).

The module `Langlands.Theta.WeilIndex.Defs` defines the Weil index of a character of second degree
on a totally disconnected group and proves that it has modulus one, that the regularized integral
of the character for any Haar measure is a positive multiple of it, and the book's Theorem 3.3.

## Setting

`X` is a commutative, locally compact, second countable topological group with arbitrarily large
and small compact open subgroups (`CompactOpenExhaustion`). The main example is a
finite-dimensional vector space over a nonarchimedean local field `F` with its module topology
(`compactOpenExhaustion_of_finiteDimensional` and the neighbouring lemmas of
`HarmonicAnalysis/Bicharacter/SelfDual.lean`). No hypothesis on the characteristic of `F` is used.

## Content

- `secondDegreeBicharacter f x y = f(x + y) f(x)⁻¹ f(y)⁻¹` (GKT (3.6)).
- `IsCharacterOfSecondDegree f`: `f : X → ℂ` is locally constant, of modulus one, and its
  bicharacter is self-dual (`IsSelfDualBicharacter`): Weil's non-degenerate character of second
  degree (Remark 3.1). `of_bicharacter`: a locally constant `f` of modulus one with
  `f(x + y) = f(x) f(y) e(x, y)` for a self-dual `e` is one, and then `secondDegreeBicharacter f = e`
  (`secondDegreeBicharacter_eq`). `map_add`, `map_zero` (`f(0) = 1`), `subset_annihilator`.
- **Quadratic forms** (the book's case): `isCharacterOfSecondDegree_quadraticForm`: for a
  nonarchimedean local field `F`, a non-trivial continuous character `ψ : F → ℂ¹` and a quadratic
  form `q` on a finite-dimensional `F`-space whose polar form is non-degenerate
  (`(QuadraticMap.polarBilin q).SeparatingLeft`), `x ↦ ψ(q x)` is a character of second degree with
  bicharacter `ψ ∘ polar q` (`secondDegreeBicharacter_quadraticForm`, `continuous_quadraticForm`).
  In the book's notation `q = ½ q_b`, `polar q = b`, `f = f_b = ψ ∘ ½ q_b`.
- **Integrals over compact open subgroups** (the computation in the proof of Proposition 3.10):
  `setIntegral_eq_setIntegral_annihilator`: if `f = 1` on a compact open subgroup `M`, then
  `∫_L f dμ = ∫_{M^⊥} f dμ` for every compact open subgroup `L ⊇ M^⊥`. Proof: for `m ∈ M`,
  `∫_L f(x) e(x, m) dx = ∫_L f(x + m) dx = ∫_L f`; averaging over `M` (Fubini) and
  `∫_M e(x, m) dm = μ(M) 1_{M^⊥}(x)` (`bicharacterFourier_indicator`) give `μ(M) ∫_L f = μ(M) ∫_{M^⊥} f`.
  Hence `exists_setIntegral_eq` (the integrals stabilize), `exists_hasGaussIntegral`,
  `hasGaussIntegral_unique`.
- **The modulus**: `hasGaussIntegral_mul_conj`: the Gauss integral `γ_μ` (`HasGaussIntegral μ f γ_μ`)
  satisfies `γ_μ conj(γ_μ) = C(μ)`, the constant of Fourier inversion
  (`bicharacterFourierConstant`). Proof: take `M = N^⊥` with `f = 1` on `M` (from `small`), so that
  `M^⊥⊥ = M`, and a compact open subgroup `L ⊇ M^⊥` with `∫_L f = γ_μ`; then `L^⊥ ⊆ M ⊆ L` and
  `|∫_L f|² = ∫_{y ∈ L} ∫_{u ∈ L} f(u) e(u, y) = μ(L) ∫_{L^⊥} f = μ(L) μ(L^⊥)`, which is `C(μ)`
  (`bicharacterFourierConstant_eq_measureReal_mul`, from `ℱℱ1_L(0)`). So `γ_μ ≠ 0`
  (`hasGaussIntegral_ne_zero`) and `‖γ_μ‖ = C(μ)^{1/2}` (`norm_hasGaussIntegral`). In the book's
  notation `C(dx) = |β_b|⁻¹`, so this is the positivity statement of Lemma 3.9 and Proposition 3.10
  with the positive scalar made explicit.
- `weilIndex f`: **the Weil index** (Definition 3.4), defined as the Gauss integral of `f` for the
  self-dual measure of its bicharacter (`selfDualMeasure`, GKT Proposition 1.39; `1` if there is
  none):
  - `hasGaussIntegral_selfDualMeasure_weilIndex`; `hasGaussIntegral_weilIndex`: for every Haar
    measure `μ` the Gauss integral is `C(μ)^{1/2} γ(f)`;
  - `norm_weilIndex`: `‖γ(f)‖ = 1`; `weilIndex_ne_zero`;
  - `weilIndex_eq_div_norm` (Corollary 3.12): `γ(f) = γ_μ / ‖γ_μ‖` for the Gauss integral `γ_μ` of
    any Haar measure;
  - `setIntegral_eq_weilIndex` (Proposition 3.10): if `f = 1` on a compact open subgroup `M`, then
    `∫_L f dμ = C(μ)^{1/2} γ(f)` for every compact open subgroup `L ⊇ M^⊥`;
  - `weilIndex_eq_one` (Corollary 3.11): `γ(f) = 1` if `f = 1` on a compact open subgroup `L` with
    `L^⊥ = L`.
- **Theorem 3.3**: `bicharacterFourier_convolution`: for a Schwartz–Bruhat function `φ`,
  `ℱ_μ(φ ∗ f) = C(μ)^{1/2} γ(f) · ℱ_μ φ · f⁻¹`, `(φ ∗ f)(x) = ∫ φ(z) f(x - z) dμ(z)`; this is (3.9)
  `|β_b|^{1/2} (φ ∗ f_b)^ = γ(f_b) φ̂ · f_b^*` on `X` through `β_b`, with `f_b^*(β_b y) = f_b(y)⁻¹`.
  Proof: `φ ∗ f = f · ℱ_μ(φ(-·) f)` and Weil's formula (`bicharacterFourier_mul_bicharacterFourier`)
  with `g = f⁻¹`, `s = id`. The book proves Theorem 3.3 by the Stone–von Neumann theorem and
  defines `γ` by it; here `γ` is defined by the Gauss integral and Theorem 3.3 is derived.
  `integral_convolution` (Corollary 3.6) is its value at `0`.
- **Proposition 3.13 (a)**: `IsCharacterOfSecondDegree.comp_addEquiv`,
  `weilIndex_comp_addEquiv`: `γ(f ∘ T) = γ(f)` for an additive homeomorphism `T`.
- **Proposition 3.13 (d)** (orthogonal sums): `IsSelfDualBicharacter.pi`,
  `IsCharacterOfSecondDegree.pi`, `weilIndex_pi`: `γ(x ↦ ∏ᵢ fᵢ(xᵢ)) = ∏ᵢ γ(fᵢ)` on `ι → X`;
  `CompactOpenExhaustion.pi`.
- `HasGaussIntegral.smul_measure`: Gauss integrals for `rμ` are `r` times those for `μ`.

The book's Remark 3.5 (p. 76) writes `f̂_b = γ(f_b) |β_b|^{-1/2} f_b^* ∈ C_c^∞(X^*)`; `f̂_b` has
constant modulus `|β_b|^{-1/2}`, so it is a locally constant function (a distribution), not a
compactly supported one. Remark 3.5 is not formalized.

## Literature

W. T. Gan, S. S. Kudla, S. Takeda, *The Local Theta Correspondence* (book draft, 2025), chapter 3:
3.1.3, (3.6) and Remark 3.1, p. 71; Theorem 3.3, p. 73; Definition 3.4 and Corollary 3.6, p. 76;
Proposition 3.10, p. 79; Corollaries 3.11 and 3.12, p. 80; Proposition 3.13, p. 81.

## Declarations

- `Langlands.Theta.secondDegreeBicharacter`, `IsCharacterOfSecondDegree`, `weilIndex`,
  `HasGaussIntegral.smul_measure`.
- `IsCharacterOfSecondDegree.ne_zero`, `.map_add`, `.map_zero`, `.continuous`, `.mul_conj`,
  `secondDegreeBicharacter_eq`, `.of_bicharacter`, `.subset_annihilator`,
  `.isCompact_annihilator`, `.setIntegral_eq_setIntegral_annihilator`,
  `.exists_addSubgroup_eq_one`, `.exists_setIntegral_eq`, `.exists_hasGaussIntegral`,
  `.hasGaussIntegral_unique`, `.bicharacterFourierConstant_eq_measureReal_mul`,
  `.hasGaussIntegral_mul_conj`, `.hasGaussIntegral_ne_zero`, `.norm_hasGaussIntegral`.
- `hasGaussIntegral_weilIndex`, `hasGaussIntegral_selfDualMeasure_weilIndex`, `norm_weilIndex`,
  `weilIndex_ne_zero`, `weilIndex_eq_div_norm`, `setIntegral_eq_weilIndex`, `weilIndex_eq_one`,
  `bicharacterFourier_convolution`, `integral_convolution`.
- `IsCharacterOfSecondDegree.comp_addEquiv`, `weilIndex_comp_addEquiv`.
- `Langlands.HarmonicAnalysis.CompactOpenExhaustion.pi`,
  `Langlands.HarmonicAnalysis.IsSelfDualBicharacter.pi`, `IsCharacterOfSecondDegree.pi`,
  `weilIndex_pi`.
- `continuous_quadraticForm`, `secondDegreeBicharacter_quadraticForm`,
  `isCharacterOfSecondDegree_quadraticForm`.

## Dependencies

`Langlands.HarmonicAnalysis.Bicharacter.SelfDualMeasure`,
`Langlands.HarmonicAnalysis.Bicharacter.GaussIntegral`; Mathlib:
`LinearAlgebra.QuadraticForm.Basis` (`LinearMap.BilinMap.toQuadraticMap_surjective`).
