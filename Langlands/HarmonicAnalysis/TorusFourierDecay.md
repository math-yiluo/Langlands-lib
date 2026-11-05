# Rapid decay of Fourier coefficients of smooth functions on a finite product of circles

Lean module: `Langlands.HarmonicAnalysis.TorusFourierDecay`, namespace
`Langlands.HarmonicAnalysis.TorusFourier`. It imports the published
`Langlands.Representation.Plancherel.RationalOrbitSmoothFunctions` for the real-angle covering
`finiteTorusExp x = (e^{i x_j})_j` of `J → Circle` (`finiteTorusExp_add`,
`isOpenQuotientMap_finiteTorusExp`) and for the Library's smoothness predicate
`IsSmoothFiniteTorusFunction f`, which means `f ∘ finiteTorusExp` is `C^∞` on `J → ℝ`. From
Mathlib it uses `hasDerivAt_integral_of_dominated_loc_of_deriv_le`
(`Mathlib.Analysis.Calculus.ParametricIntegral`), `integral_mul_right_eq_self`
(`Mathlib.MeasureTheory.Group.Integral`), `contDiff_infty_iff_fderiv` and
`norm_integral_le_of_norm_le_const`.

## Provenance

Waldspurger, *La formule de Plancherel pour les groupes p-adiques, d'après Harish-Chandra*,
J. Inst. Math. Jussieu 2 (2003), 235–333, DOI 10.1017/S1474748003000082, proof of
Proposition VI.3.1, printed p. 303 (PDF p. 69), estimate (4):

> La théorie usuelle de la transformation de Fourier sur le groupe abélien compact
> `Im X(G)` nous dit qu'il existe `D ∈ 𝒟^G` tel que pour tout `φ′ ∈ C^∞(Im X(G))` et tout
> `g ∈ G`, on ait
> `|∫_{Im X(G)} φ′(λ) λ(g) dλ| ⩽ (1 + (H_G(g)))^{-r} ν^G(D, φ′)`.   (4)

The page image prints `(1 + (H_G(g)))^{-r}` in (4). The next display on the same page has
`(1 + |H_G(g)|)^{-r}`, so (4) is read with `|H_G(g)|`. Here `r ∈ ℝ` is fixed earlier in the
proof. Printed p. 302 (PDF p. 68) defines `𝒟^M` as "l'ensemble des ensembles finis
d'opérateurs différentiels sur `Im X(M)`, à coefficients constants" and
`ν^M(D, φ) = sup{|dφ(χ)|; d ∈ D, χ ∈ Im X(M)}`. `𝒟^G` and `ν^G` are the same objects for
`M = G`.

Waldspurger gives no proof of (4) and cites the usual Fourier theory. This module proves the
estimate for a torus written in coordinates, `T = J → Circle` with `J` finite. The proof is the
standard integration by parts. It is derived for this purpose and does not follow a cited text.

## Scope and hypotheses

`J` is a finite type (`Fintype J`); `DecidableEq J` is assumed wherever `Pi.single` occurs. The
torus is `J → Circle` with its product group structure. The norm on `J → ℤ` is the sup norm,
so `‖n‖ = max_j |n_j|`.

Not made here:

- the identification of Waldspurger's `Im X(G)` with `J → Circle`;
- the identification of `λ ↦ λ(g)` with a character `torusCharacter n(g)`, where `n(g)` is the
  lattice point determined by `H_G(g)`;
- the comparison of `|H_G(g)|` with `‖n(g)‖`;
- the general element of `𝒟^G`. The operators used here are the identity and the iterated
  angle derivatives `∂_j^k`, which are constant-coefficient operators on the torus.

Hypotheses of the results:

- `torusCharacter_mul`, `norm_torusCharacter`, `continuous_torusCharacter`,
  `finiteTorusExp_zero`, `torusCharacter_finiteTorusExp_single`, `one_add_norm_pow_le`: none.
- `hasDerivAt_comp_finiteTorusExp`, `torusPartialDeriv_finiteTorusExp`,
  `hasDerivAt_torusTranslate`, `isSmoothFiniteTorusFunction_torusPartialDeriv`,
  `isSmoothFiniteTorusFunction_iterate_torusPartialDeriv`, `exists_norm_le_of_isSmooth`:
  `hf : IsSmoothFiniteTorusFunction f`.
- `integral_translate_mul_torusCharacter`: `μ` is a left-invariant measure on `J → Circle`
  (`[μ.IsMulLeftInvariant]`). There is no hypothesis on `f`.
- `norm_torusFourierCoeff_le`: `μ` is a finite measure (`[IsFiniteMeasure μ]`), and
  `hM : ∀ z, ‖f z‖ ≤ M`.
- `torusFourierCoeff_torusPartialDeriv`, `torusFourierCoeff_iterate_torusPartialDeriv`:
  `μ` finite and left-invariant, and `hf : IsSmoothFiniteTorusFunction f`.
- `abs_pow_mul_norm_torusFourierCoeff_le`: `μ` finite and left-invariant, `hf`, and
  `hM : ∀ z, ‖(∂_j)^[k] f z‖ ≤ M`.
- `one_add_norm_pow_mul_norm_torusFourierCoeff_le`: `μ` finite and left-invariant, `hf`,
  `hM0 : ∀ z, ‖f z‖ ≤ M` and `hM : ∀ j z, ‖(∂_j)^[k] f z‖ ≤ M`.
- `norm_torusFourierCoeff_le_rpow`: the same hypotheses for some `k : ℕ`, and `hr : r ≤ k`
  for the real exponent `r`.

## Definitions

- `torusCharacter n z = ∏_j z_j^{n_j}` (in `ℂ`), for `n : J → ℤ` and `z : J → Circle`.
- `torusPartialDeriv j f z = deriv (θ ↦ f(z · finiteTorusExp (Pi.single j θ))) 0`: the
  derivative of `f` at `z` along the `j`-th angle (written `∂_j f`). It is defined for every
  `f`; when the derivative does not exist, Mathlib's `deriv` gives `0`. The results only use it
  for smooth `f`.
- `torusFourierCoeff μ f n = ∫ f(z) torusCharacter n z dμ(z)`: the Fourier coefficient of `f`
  at `n`. It is a Bochner integral, so it is `0` when the integrand is not integrable.

## Results

- `torusCharacter_mul`: `χ_n(z w) = χ_n(z) χ_n(w)`, where `χ_n = torusCharacter n`.
- `norm_torusCharacter`: `|χ_n(z)| = 1`.
- `continuous_torusCharacter`: `χ_n` is continuous.
- `finiteTorusExp_zero`: `finiteTorusExp 0 = 1`.
- `torusCharacter_finiteTorusExp_single`: `χ_n(finiteTorusExp (Pi.single j θ)) = e^{i n_j θ}`.
- `hasDerivAt_comp_finiteTorusExp`: for smooth `f`, the derivative of
  `t ↦ f(finiteTorusExp x · finiteTorusExp (Pi.single j t))` at `θ` is
  `D(f ∘ finiteTorusExp)(x + θ e_j)(e_j)`, where `e_j = Pi.single j 1`.
- `torusPartialDeriv_finiteTorusExp`: `∂_j f (finiteTorusExp x) = D(f ∘ finiteTorusExp)(x)(e_j)`.
- `hasDerivAt_torusTranslate`: the derivative of `t ↦ f(z · finiteTorusExp (Pi.single j t))`
  at `θ` is `∂_j f (z · finiteTorusExp (Pi.single j θ))`.
- `isSmoothFiniteTorusFunction_torusPartialDeriv`,
  `isSmoothFiniteTorusFunction_iterate_torusPartialDeriv`: `∂_j f` and `∂_j^k f` are smooth.
- `exists_norm_le_of_isSmooth`: a smooth `f` is bounded.
- `integral_translate_mul_torusCharacter`: translation in the `j`-th angle multiplies the
  coefficient by a phase:
  `∫ f(z · finiteTorusExp (Pi.single j θ)) χ_n(z) dμ = f̂(n) e^{-i n_j θ}`.
- `torusFourierCoeff_torusPartialDeriv` (**integration by parts**):
  `(∂_j f)^(n) = -(i n_j) f̂(n)`.
- `torusFourierCoeff_iterate_torusPartialDeriv`: `(∂_j^k f)^(n) = (-(i n_j))^k f̂(n)`.
- `norm_torusFourierCoeff_le`: `|f̂(n)| ≤ M μ(T)`, where `μ(T)` is `μ.real univ`.
- `abs_pow_mul_norm_torusFourierCoeff_le`: `|n_j|^k |f̂(n)| ≤ M μ(T)`.
- `one_add_norm_pow_le`: `(1 + ‖n‖)^k ≤ 2^k (1 + ∑_j |n_j|^k)`.
- `one_add_norm_pow_mul_norm_torusFourierCoeff_le` (**rapid decay**):
  `(1 + ‖n‖)^k |f̂(n)| ≤ 2^k (1 + |J|) M μ(T)`.
- `norm_torusFourierCoeff_le_rpow` (**estimate (4) in coordinates**): for real `r ≤ k`,
  `|f̂(n)| ≤ 2^k (1 + |J|) M μ(T) (1 + ‖n‖)^{-r}`.

In terms of Waldspurger's (4): take `D` to be the identity and the operators `∂_j^k` for
`j ∈ J`, each multiplied by the constant `2^k (1 + |J|) μ(T)`. With `M = ν^G` of the
unscaled operators, the right-hand side of `norm_torusFourierCoeff_le_rpow` is
`(1 + ‖n‖)^{-r} ν^G(D, f)`.

## Proof notes

1. `hasDerivAt_comp_finiteTorusExp`: `f ∘ finiteTorusExp` is differentiable (from `C^∞`). The
   curve `t ↦ x + Pi.single j t` has derivative `e_j` (`ContinuousLinearMap.single`). The chain
   rule applies, and `finiteTorusExp_add` rewrites `finiteTorusExp (x + Pi.single j t)` as the
   product. At `θ = 0` this gives `torusPartialDeriv_finiteTorusExp`. Since `finiteTorusExp` is
   surjective, every `z` has the form `finiteTorusExp x`, which gives `hasDerivAt_torusTranslate`.
2. `isSmoothFiniteTorusFunction_torusPartialDeriv`: by step 1, `∂_j f ∘ finiteTorusExp` is
   `x ↦ D(f ∘ finiteTorusExp)(x)(e_j)`. This is `C^∞` because the derivative of a `C^∞` map is
   `C^∞` (`contDiff_infty_iff_fderiv`), applied to the constant vector `e_j`. Induction on `k`
   gives the iterated version.
3. `integral_translate_mul_torusCharacter`: write `e = finiteTorusExp (Pi.single j θ)`. Then
   `e · finiteTorusExp (Pi.single j (-θ)) = 1`, so
   `f(z e) χ_n(z) = f(z e) χ_n(z e) χ_n(finiteTorusExp (Pi.single j (-θ)))`. The torus is
   commutative, so the left-invariant `μ` is right-invariant, and `integral_mul_right_eq_self`
   removes the translation. The constant factor is `e^{-i n_j θ}`.
4. `torusFourierCoeff_torusPartialDeriv`: let `F(θ) = ∫ f(z e_θ) χ_n(z) dμ`. Its integrand
   has θ-derivative `∂_j f(z e_θ) χ_n(z)` (step 1). This derivative is bounded by a bound for
   `∂_j f`, which is integrable because `μ` is finite. So
   `hasDerivAt_integral_of_dominated_loc_of_deriv_le` differentiates under the integral at
   `θ = 0`, and `F′(0) = (∂_j f)^(n)`. By step 3, `F(θ) = f̂(n) e^{-i n_j θ}`, with derivative
   `-(i n_j) f̂(n)` at `0`. Uniqueness of derivatives gives the identity. Iterating it
   (smoothness from step 2) gives `torusFourierCoeff_iterate_torusPartialDeriv`.
5. `norm_torusFourierCoeff_le`: `|f χ_n| ≤ M` and `norm_integral_le_of_norm_le_const`.
   `abs_pow_mul_norm_torusFourierCoeff_le` applies this to `∂_j^k f` and uses step 4, with
   `|-(i n_j)| = |n_j|`.
6. `one_add_norm_pow_le`: if `‖n‖ ≤ 1` then `(1 + ‖n‖)^k ≤ 2^k`. Otherwise `J` is nonempty, the
   sup norm is attained at some `j` (`Finset.exists_mem_eq_sup`), and
   `(1 + ‖n‖)^k ≤ (2‖n‖)^k = 2^k |n_j|^k`.
7. `one_add_norm_pow_mul_norm_torusFourierCoeff_le`: multiply step 6 by `|f̂(n)|` and bound
   `|f̂(n)|` and each `|n_j|^k |f̂(n)|` by `M μ(T)` (step 5).
   `norm_torusFourierCoeff_le_rpow` follows because `(1 + ‖n‖)^{-r} (1 + ‖n‖)^k ≥ 1` for
   `r ≤ k` (`Real.rpow_add`, `Real.one_le_rpow`).

## Relation to the Library

`RationalOrbitSmoothFunctions` defines the torus covering and the smoothness predicate used
here. It has no Fourier coefficients or derivatives. `DiscreteFourierUniqueness` proves
uniqueness of Fourier coefficients on `ℤ^d` and on finitely generated abelian groups, which is
the converse direction (no decay). A search of the Library for `fourierCoeff`, torus characters
and differentiation under the integral on `Circle` found no decay estimate. Mathlib's
`fourierCoeffOn_of_hasDerivAt` (`Mathlib.Analysis.Fourier.AddCircle`) is the one-variable
integration by parts on an interval for `AddCircle`. It does not cover several variables or
the multiplicative `Circle` with a general invariant measure.

## Open obligations

Applying this to the proof of Proposition VI.3.1 requires the identifications listed as not
made under Scope: `Im X(G) ≅ J → Circle`, `λ(g) = torusCharacter n(g) λ`, and
`|H_G(g)| ≍ ‖n(g)‖`. The remaining steps of Proposition VI.3.1 are not addressed here.
