# Right convolution of Eisenstein series where the series converges

Module `Langlands.Global.AdelicEisensteinConvolutionIdentity` (namespace
`Langlands.Global.AdelicGroupPoints`) defines the integrated normalized induced action
`I(λ, φ)` and proves, for parameters at which the terms of the Eisenstein series are dominated
by a summable sequence, the identity `R(φ) E(v, λ) = E(I(λ, φ) v, λ)`, and the linearity of the
Eisenstein series in the inducing function where its terms are summable.

| Declaration | Kind | Source |
| --- | --- | --- |
| `IsIwasawaCompact.inducedConvolution` | definition | Arthur 2005 §7, p.33; MW IV.1.7 (*) |
| `IsIwasawaCompact.parameterTwist_inducedConvolution` | theorem | internal |
| `IsIwasawaCompact.rightConvolution_eisensteinSeries_eq_inducedConvolution` | theorem | Arthur 2005 §7, p.34 |
| `IsIwasawaCompact.eisensteinSeries_sum_mul` | theorem | internal |

## Notation

`hK : IsIwasawaCompact p K` is a compact subgroup `K` of `G(𝔸)` with `P(𝔸) K = G(𝔸)` and Iwasawa
height `H_P` (`hK.height`). `hK.heightPower λ g = exp⟨λ, H_P(g)⟩`,
`hK.parameterTwist v λ g = v(g) exp⟨λ, H_P(g)⟩`, and the Eisenstein series is
`hK.eisensteinSeries v λ g = ∑_{γ ∈ P(F) \ G(F)} v(γ g) exp⟨λ, H_P(γ g)⟩`, an unconditional
sum which is `0` when the terms are not summable (module
`Langlands.Global.AdelicEisensteinSeries`). The twisted right translate
`hK.inducedRightTranslate λ h v (g) = exp⟨-λ, H_P(g)⟩ · v(g h) exp⟨λ, H_P(g h)⟩` is
`I_P(λ, h) v` of module `Langlands.Global.AdelicInducedRightTranslate`, in Lapid's normalization
where the half-modulus is part of `v`. `rightConvolution F G φ f (x) = ∫ φ(h) f(x h) dh` is the
right convolution of module `Langlands.Global.AdelicLocalFinitenessStatement`, for
`Measure.haar` on `G(𝔸)`.

## Definition

`hK.inducedConvolution λ φ v (y) = ∫ φ(h) · hK.inducedRightTranslate λ h v (y) dh`, the
Bochner integral for `Measure.haar` on `G(𝔸)`. Thus
`I(λ, φ) v (y) = ∫ φ(h) v(y h) exp⟨λ, H_P(y h) − H_P(y)⟩ dh`.

Provenance. J. Arthur, *An introduction to the trace formula*, in *Harmonic Analysis, the Trace
Formula, and Shimura Varieties*, Clay Math. Proc. 4 (2005), registered as
`arthur-ellwood-kottwitz-2005-harmonic-analysis-shimura`, §7, printed p.33 (PDF p.45): the
operator `(I_P(λ, y) φ)(x) = φ(x y) e^{(λ+ρ_P)(H_P(x y))} e^{-(λ+ρ_P)(H_P(x))}` on the inducing
data. Absorbing the half-modulus into the inducing function, `v = e^{ρ_P(H_P(·))} φ`, turns this
operator into `hK.inducedRightTranslate λ y`:
`e^{ρ_P(H_P(x))} (I_P(λ, y) φ)(x) = v(x y) e^{⟨λ, H_P(x y) − H_P(x)⟩}`. The definition
integrates these operators against `φ` for Haar measure, which is the integrated form of
Arthur's representation `I_P(λ)`. C. Mœglin and J.-L. Waldspurger, *Spectral decomposition and
Eisenstein series* (1995), registered as `moeglin-waldspurger-1995-spectral-decomposition`,
IV.1.7, p.139, define the corresponding action `i(π, h)` of the Hecke algebra on the inducing
data, "a multiple of the induced representation", and relation (*) compares `E(i(π, h) φ, π)`
with the convolution of `E(φ, π)` by `h`.

## Results

- `parameterTwist_inducedConvolution`: `(I(λ, φ) v)_λ (y) = ∫ φ(h) v_λ(y h) dh`, where
  `v_λ = hK.parameterTwist v λ`. Proof: move the factor `exp⟨λ, H_P(y)⟩` under the integral
  (`integral_mul_const`) and use `parameterTwist_inducedRightTranslate`.
- `rightConvolution_eisensteinSeries_eq_inducedConvolution`: let `φ` be continuous with
  compact support, `v` continuous, `λ` a parameter and `x ∈ G(𝔸)`, and suppose that a summable
  sequence `b` bounds the terms: `‖v_λ(γ_c x h)‖ ≤ b c` for every coset `c ∈ P(F) \ G(F)`
  (with its chosen representative `γ_c`) and every `h ∈ tsupport φ`. Then
  `rightConvolution F G φ (hK.eisensteinSeries v λ) x = hK.eisensteinSeries (I(λ, φ) v) λ x`.
  This is Arthur's identity `E(x, I_P(λ, y) φ, λ) = E(x y, φ, λ)` (§7, printed p.34, PDF p.46)
  integrated against `φ`, in the region where the series converge.

  Proof as implemented. The published
  `IsIwasawaCompact.rightConvolution_eisensteinSeries` (module
  `Langlands.Global.AdelicEisensteinHarishChandraEquations`) exchanges, under the same
  hypotheses, the convolution and the sum over `P(F) \ G(F)`:
  `rightConvolution F G φ (hK.eisensteinSeries v λ) x = ∑_c rightConvolution F G φ v_λ (γ_c x)`.
  The `c`-th term `∫ φ(h) v_λ(γ_c x h) dh` is `(I(λ, φ) v)_λ(γ_c x)` by
  `parameterTwist_inducedConvolution`, which is the `c`-th term of `E(I(λ, φ) v, λ)(x)`.
- `eisensteinSeries_sum_mul`: for finitely many `w i` and scalars `b i` such that every series
  `c ↦ (w i)_λ(γ_c x)` is summable,
  `hK.eisensteinSeries (fun y => ∑ i, b i * w i y) λ x = ∑ i, b i * hK.eisensteinSeries (w i) λ x`.
  Proof: the terms are linear in the inducing function, and a finite sum of summable series
  is summed termwise (`Summable.tsum_finsetSum`, `tsum_mul_left`).

The summability hypotheses hold for automorphic `v` and sufficiently regular `λ` by the
Library's `eisensteinAbsoluteConvergence` (module
`Langlands.Global.AdelicEisensteinConvergenceProof`; Mœglin–Waldspurger II.1.5), which gives a
summable majorant uniform for `g` in a compact set. No continuation is asserted here.
