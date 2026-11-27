# Finite square-integrable span on the imaginary axis from a common center ideal

`Langlands.Global.NormalizedConvolutionImaginarySpanReductionStatement` is the implication

```
InducedConvolutionUniformCenterIdealStatement →
  ParabolicHarishChandraFinitenessStatement.{0} →
    NormalizedConvolutionImaginarySpanStatement
```

and `normalizedConvolutionImaginarySpanReduction` proves it. The first premise, in
`Langlands.Global.AdelicInducedConvolutionFiniteSpanReduction`, asks for one ideal of finite
complex codimension in the ambient enveloping center that annihilates every plot-smooth infinite
slice of the integrated induced action `hK.inducedConvolution λ φ v`, for every complex
parameter `λ`. The second premise is Harish-Chandra's finiteness theorem on
`U(𝔸) M(F) \ G(𝔸)` in the form of `Langlands.Automorphic.GroupSchemeHarishChandraFinitenessStatement`.
This module proves the implication and neither premise.

The conclusion `NormalizedConvolutionImaginarySpanStatement`, in
`Langlands.Global.AdelicNormalizedConvolutionHolomorphy`, keeps the supplied presented parabolic,
geometric unipotent radical, Levi retraction, maximal compact `K` with `P(𝔸) K = G(𝔸)` and
compatible Haar measure. The proof does not use a minimal parabolic in Iwasawa position for `K`,
the Levi retraction or the compatible measure. The normalized convolution in the conclusion,
`g ↦ ∫ φ(h) T_{λ,h} v (g) dh` with `T_{λ,h} = hK.inducedRightTranslate λ h`, is by definition
`hK.inducedConvolution λ φ v`.

## Implemented proof

Fix `v ∈ A²_P` and a left-finite test function `φ`, and write `f_λ = hK.inducedConvolution λ φ v`.

1. *Parabolic data.* The root presentation supplies `IsParabolicSubgroup p` and
   `IsRationalLeviSubgroup l` (fields `parabolic` and `levi` of `r.isCompatible`); the Levi is
   then connected reductive. The multiplication isomorphism for the given radical is a hypothesis
   of the statement.
2. *Common compact data.* `inducedConvolutionCompactData` gives one open subgroup `L` of
   `G(𝔸_f)` and one finite-dimensional space `E` of functions on `K_∞` such that, for every `λ`,
   `f_λ` is right `L`-invariant, right `K_∞`-finite, and every function `k ↦ f_λ(g k)` lies in
   `E`.
3. *Common center ideal.* The input `v` is smooth, left invariant under `U(𝔸)` and finite under
   the enveloping center, so the first premise gives one ideal `J` of finite codimension that
   annihilates the plot-smooth infinite slices of every `f_λ`.
4. *Membership in `A²_P`.* `inducedConvolutionParabolicCovariance` gives left invariance under
   `U(𝔸) M(F)` and split-component equivariance of each `f_λ`.
   `IsIwasawaCompact.continuous_inducedConvolution`, `inducedConvolutionSmoothSlices` and
   `IsIwasawaCompact.hasModerateGrowthFunction_inducedConvolution` give continuity, plot-smooth
   infinite slices and moderate growth; with steps 2 and 3, each `f_λ` is automorphic on
   `U(𝔸) M(F) \ G(𝔸)`. `inducedConvolutionWeightedSquare` gives the weighted square
   integrability in the canonical Levi quotient norm. Hence every `f_λ` lies in `A²_P`.
5. *Finiteness.* By steps 2–4 every `f_λ` satisfies the four conditions of the finiteness
   theorem for `J`, `L` and `E`, so the span of all `f_λ` is finite-dimensional.
6. *Choice of the family.* `Submodule.fg_span_iff_fg_span_finset_subset` gives a finite set `s`
   of values `f_λ` with the same span as all of them. Enumerating `s` gives the family `u`; each
   `u j` is some `f_λ` and lies in `A²_P` by step 4. For a real parameter `x`, the value at the
   imaginary parameter `imaginaryParameter F P x` is one of the `f_λ`, hence lies in the span of
   `u`.

The family is chosen once, independently of `x`; the argument gives a common finite span on the
whole complex parameter space, of which the imaginary axis is a part.

## Provenance

The route is Mœglin–Waldspurger, *Spectral Decomposition and Eisenstein Series* (1995), I.2.17,
printed pp. 37–38 (chapter file `05.2_pp_18_40_Automorphic_forms_growth_constant_terms.pdf`,
PDF pp. 20–21), registered as `moeglin-waldspurger-1995-spectral-decomposition`: automorphic
forms on `U(𝔸) M(k) \ G` with fixed `K`-types annihilated by a fixed ideal of finite
codimension of the center form a finite-dimensional space ("the finiteness theorem (see [HC]
Theorem 1)" generalised to these quotients, p. 38). The two premises are that finiteness theorem
and the uniform center ideal obtained from the relation between the center and the Levi center
on p. 37. The integrated action is the normalized action of Arthur, *An introduction to the
trace formula* (2005), §7, printed pp. 32–34, with the half-modulus in the inducing form as in
Lapid, *On the asymptotic inner product of truncated Eisenstein series* (2011), §2, p. 311.
