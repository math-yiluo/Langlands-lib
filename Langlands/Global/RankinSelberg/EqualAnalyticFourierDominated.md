# Fourier transforms of Schwartz–Bruhat functions are dominated

Module `Langlands.Global.RankinSelberg.EqualAnalyticFourierDominated`, namespace
`Langlands.Global.RankinSelbergGlobal.EqualAnalytic`.

For a standard character `ψ` and `Φ ∈ S(𝔸^n)`, consider the Library's Fourier transform
`fourierTransform F n ψ Φ (η) = ∫ Φ(y) ψ(Σ_j y_j η_j) d(rectangleMeasure F 1 n)`. It is continuous
and dominated (`fourierTransform_properties`).

## Provenance

Internal. The tensor factorization and the support argument are the standard computation of the
Fourier transform of a Schwartz–Bruhat function (Tate's thesis, §4.1). They are derived from the
modules `EqualAnalyticCharacter`, `EqualAnalyticProduct`, `EqualAnalyticArchimedeanFourier` and
`EqualAnalyticFiniteAdeles`, and from the Library's description of `ψ₀`.

## Declarations

- `infiniteAdele`, `finiteAdele`, `addChar_eq_infinite_mul_finite`: `ψ(x) = ψ(x_∞, 0) ψ(0, x_f)`.
- `unitExp_eq_fourierChar`: the Library's `unitExp` is Mathlib's `𝐞`.
- `standardCharacter_mul_infiniteAdele`: `ψ₀(b (u, 0)) = 𝐞(Tr_∞(b u))` in mixed coordinates.
- `finiteCharacter F ψ t = ψ(0, t)`, with `finiteCharacter_add`, `finiteCharacter_eq`
  (`ψ = ψ₀(b ·)` gives `ψ₀(0, b t)`), `norm_finiteCharacter`, and
  `standardCharacter_mul_finiteAdele`.
- `exists_dual_denominator_finite`: there is a nonzero `D ∈ 𝒪` such that `ψ₀(0, z c) = 1` for
  all `c ∈ Ô` implies `D z ∈ Ô`. Write `z = r + c'` with `r ∈ F` and `c' ∈ Ô`. Then
  `Tr(r 𝒪) ⊆ ℤ` (Library `adelicCharacter_finiteToAdeles`), and the Library's
  `exists_dual_denominator` applies.
- `adeles_sum_fst`, `adeles_sum_snd`: projections of finite sums of adeles.
- `addChar_rowPairing`: `ψ(Σ_j y_j η_j)` is the product of the archimedean trace character and the
  finite factor.
- `fourierTransform_pure`: for a pure tensor,
  `Φ̂(η) = rowConstant • (∫ Φ_∞(e) 𝐞(Tr_∞(b Σ_j e_j η_j)) de) · (∫ Φ_f(a) ψ(0, Σ_j a_j η_j) da)`.
- `exists_finiteFourier_support`: the finite factor vanishes unless `d η_{j,f} ∈ Ô` for all `j`.
  Translation invariance of `Φ_f` under `(N Ô)^n` multiplies the integral by `ψ(0, N c η_j)`.
  A nonzero integral therefore forces these values to be `1`. The dual denominator lemma then
  applies, with `b = p/q`.
- `integrable_mul_pairing`, `fourierTransform_add`, `fourierTransform_smul`, `fourierTransform_zero`:
  linearity on integrable functions.
- `continuous_fourierTransform`: the transform of an integrable function is continuous
  (dominated convergence).
- `isRowDominated_fourierTransform_pure` and `fourierTransform_properties`: `Φ̂` is dominated. The
  archimedean factor decays by `exists_archimedeanFourier_decay` with `β = b`; the finite factor
  is bounded by `∫ |Φ_f|` and supported as above.
