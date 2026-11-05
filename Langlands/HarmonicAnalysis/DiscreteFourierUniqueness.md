# Uniqueness of Fourier coefficients on finitely generated abelian groups

Lean module: `Langlands.HarmonicAnalysis.DiscreteFourierUniqueness`, namespace
`Langlands.HarmonicAnalysis.DiscreteFourier`. It imports only Mathlib:
`Mathlib.Analysis.Fourier.AddCircleMulti` (`UnitAddTorus`, `UnitAddTorus.mFourier`,
`UnitAddTorus.mFourier_add`), `Mathlib.Analysis.Fourier.FiniteAbelian.PontryaginDuality`
(`AddChar.sum_apply_eq_ite`, `AddChar.norm_apply`) and
`Mathlib.GroupTheory.FiniteAbelian.Basic` (`AddCommGroup.equiv_free_prod_directSum_zmod`).
It also uses `AddCircle.haarAddCircle`, `fourierCoeff_fourier`,
`MeasureTheory.integral_fintype_prod_eq_prod`,
`MeasureTheory.integral_tsum_of_summable_integral_norm`, `Summable.tsum_prod`,
`Finsupp.linearEquivFunOnFinite` and `DFinsupp.equivFunOnFintype`.

## Provenance

Waldspurger, *La formule de Plancherel pour les groupes p-adiques, d'après Harish-Chandra*,
J. Inst. Math. Jussieu 2 (2003), 235–333, DOI 10.1017/S1474748003000082, end of VIII.5,
printed p. 332 (PDF p. 98), uses without proof: "Supposons `φ ≠ 0`. Par inversion de Fourier
sur le groupe `A_G`, il existe `χ ∈ Â_G` tel que `p_χ φ ≠ 0`." The companion module
`CentralFourierInversion` reduces that step to a discrete statement: for the
finitely generated commutative group `A_G / (A_G ∩ K)` (`K` compact open), an absolutely
summable function all of whose Fourier coefficients vanish is zero. This module proves that
discrete statement. It is the standard uniqueness theorem for Fourier coefficients. The
statement and proof here are derived for this purpose and do not follow a cited text.

## Scope and hypotheses

Characters are monoid homomorphisms `χ : Γ →* ℂˣ`; "unitary" is `∀ γ, ‖(χ γ : ℂ)‖ = 1`. On
`ℤ^d` the characters are written `m ↦ e(m · x)` for `x` in the torus `(ℝ/ℤ)^d`
(`UnitAddTorus d`), via Mathlib's `mFourier m x = ∏ i, e(m_i x_i)`. Absolute summability is the
hypothesis `Summable fun γ => ‖f γ‖`.

**Section `Torus`.** `d` is a finite type.

- `torusHaar d` (abbreviation): the product of the probability Haar measures
  `AddCircle.haarAddCircle` on `(ℝ/ℤ)^d`.
- `norm_mFourier_apply`, `integral_mFourier`: no further hypotheses.
  `integral_fourier_haarAddCircle` concerns `ℝ/ℤ` and needs no hypotheses.
- `eq_zero_of_tsum_mFourier_mul_eq_zero`: `hf : Summable fun m => ‖f m‖` and
  `h : ∀ x, ∑' m, mFourier m x * f m = 0`.

**Section `Finite`.** `T` is a finite (`Fintype`) additive commutative group.

- `eq_zero_of_sum_addChar_mul_eq_zero`: `h : ∀ ψ : AddChar T ℂ, ∑ t, ψ t * g t = 0`.

**Section `Product`.** `d` finite, `T` a finite additive commutative group.

- `eq_zero_of_tsum_mFourier_mul_addChar_mul_eq_zero`: `hf : Summable fun x => ‖f x‖` for
  `f : (d → ℤ) × T → ℂ`, and
  `h : ∀ θ ψ, ∑' x, mFourier x.1 θ * ψ x.2 * f x = 0`.

**Section `FinitelyGenerated`.** `Γ` is a commutative group (`CommGroup`).

- `exists_addEquiv_pi_int_prod_finite`, `countable_of_fg`: `[Group.FG Γ]`.
- `eq_zero_of_characterSum_eq_zero`: `[Group.FG Γ]`, `hf : Summable fun γ => ‖f γ‖`, and
  `h : ∀ χ : Γ →* ℂˣ, (∀ γ, ‖(χ γ : ℂ)‖ = 1) → characterSum f χ = 0`.

## Definitions

- `characterSum f χ = ∑' γ, χ(γ) f(γ)`: the Fourier transform of `f : Γ → ℂ` at the character
  `χ` (`Γ` a monoid). It is a `tsum`, so it is `0` when the family is not summable; in the
  results it is only used for absolutely summable `f` and unitary `χ`.
- `torusHaar d`: see above.

## Results

- `characterSum_apply`: the definition unfolded.
- `norm_mFourier_apply`: `|e(m · x)| = 1`.
- `integral_fourier_haarAddCircle`: `∫_{ℝ/ℤ} e(k t) dt` is `1` for `k = 0` and `0` otherwise.
- `integral_mFourier`: `∫_{(ℝ/ℤ)^d} e(n · x) dx` is `1` for `n = 0` and `0` otherwise.
- `eq_zero_of_tsum_mFourier_mul_eq_zero` (**uniqueness on `ℤ^d`**): an absolutely summable
  `f` on `ℤ^d` whose Fourier series vanishes at every point of the torus is zero.
- `eq_zero_of_sum_addChar_mul_eq_zero` (**uniqueness on a finite abelian group**).
- `eq_zero_of_tsum_mFourier_mul_addChar_mul_eq_zero` (**uniqueness on `ℤ^d × T`**).
- `exists_addEquiv_pi_int_prod_finite`: a finitely generated commutative group `Γ` admits an
  additive isomorphism `Additive Γ ≃+ (Fin n → ℤ) × T` with `T` a finite additive commutative
  group.
- `countable_of_fg`: a finitely generated commutative group is countable.
- `eq_zero_of_characterSum_eq_zero` (**uniqueness on a finitely generated commutative
  group**): if `f` is absolutely summable and `characterSum f χ = 0` for every unitary
  character `χ`, then `f = 0`.

## Proof notes

1. `integral_fourier_haarAddCircle`: the `0`-th Fourier coefficient of `e(k ·)`
   (`fourierCoeff_fourier`, which gives `Pi.single k 1`). `integral_mFourier`: `mFourier n x`
   is the product `∏ i, e(n_i x_i)`, so `integral_fintype_prod_eq_prod` turns the integral into
   a product of one-dimensional integrals, which is `1` exactly when every `n_i = 0`.
2. `eq_zero_of_tsum_mFourier_mul_eq_zero`: fix `k`. Multiply the vanishing series by
   `e(-k · x)` and integrate. Each term `e(-k · x) e(m · x) f(m)` is integrable with integral
   norm `|f(m)|` (the measure has mass one), so `integral_tsum_of_summable_integral_norm`
   exchanges sum and integral. By step 1 the `m`-th integral is `f(m)` for `m = k` and `0`
   otherwise, so `0 = f(k)`.
3. `eq_zero_of_sum_addChar_mul_eq_zero`: `∑_ψ ψ(-t₀) ∑_t ψ(t) g(t) = ∑_t (∑_ψ ψ(t - t₀)) g(t)
   = |T| g(t₀)` by `AddChar.sum_apply_eq_ite`; the left side is `0`.
4. `eq_zero_of_tsum_mFourier_mul_addChar_mul_eq_zero`: for each character `ψ` of `T`, the
   function `m ↦ ∑_t ψ(t) f(m, t)` is absolutely summable on `ℤ^d` (`|ψ| = 1`,
   `AddChar.norm_apply`), and its Fourier series at `θ` is the hypothesis rewritten as an
   iterated sum (`Summable.tsum_prod`, finite inner sum). Step 2 makes it `0` for every `ψ`;
   then step 3 gives `f(m, ·) = 0` for every `m`.
5. `exists_addEquiv_pi_int_prod_finite`: the structure theorem
   `AddCommGroup.equiv_free_prod_directSum_zmod` gives
   `Additive Γ ≃+ (Fin n →₀ ℤ) × ⨁ i, ZMod (p_i^{e_i})`. The direct sum over the finite index
   type is finite (`DFinsupp.equivFunOnFintype`, each `ZMod (p_i^{e_i})` finite since
   `p_i^{e_i} ≠ 0`), and `Fin n →₀ ℤ ≃ Fin n → ℤ` (`Finsupp.linearEquivFunOnFinite`).
   `countable_of_fg` follows.
6. `eq_zero_of_characterSum_eq_zero`: transport `f` along `e : Γ ≃ (Fin n → ℤ) × T` from
   step 5. For `θ` in the torus and `ψ` a character of `T`, `γ ↦ e(e(γ)₁ · θ) ψ(e(γ)₂)` is a
   unitary character of `Γ` (`MonoidHom.mk'`; multiplicativity from `mFourier_add` and
   `AddChar.map_add_eq_mul`). Its `characterSum` is the series of step 4 after reindexing by
   `e` (`Equiv.tsum_eq`), so step 4 applies.

## Relation to the Library

A search of the Library for uses of `mFourier`, `fourierCoeff`, `UnitAddTorus`,
`PontryaginDual` and character separation found no uniqueness theorem for absolutely summable
functions on `ℤ^d` or on finitely generated abelian groups. The closest result is
`Langlands.RankinSelberg.bilateralSpectralCoefficientUniqueness`, which recovers coefficients
of bilateral series in `q^{-s}` by integration over `ℝ/ℤ`; it is specific to that one-variable
weighting. The finite-group step uses Mathlib's character orthogonality directly.

## Open obligations

None for the statements of this module. Applying it to `A_G` requires that
`A_G / (A_G ∩ K)` is finitely generated for every compact open `K`. That is the hypothesis
`HasFGCompactOpenQuotients` of `CentralFourierInversion` and is not proved here.
