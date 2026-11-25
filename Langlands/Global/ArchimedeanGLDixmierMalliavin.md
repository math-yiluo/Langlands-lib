# The Dixmier–Malliavin theorem for `GL_n` of the infinite adeles

`Langlands.Global.ArchimedeanGLDixmierMalliavin`. One theorem, in the Library's completion
coordinates for `GL_n(F_∞)`.

## Statement

`Langlands.Global.ArchimedeanGL.SmoothCompactKernel.exists_eq_sum_convolution`: let `K` be a number
field, `n : ℕ`, `μ` a left Haar measure on `InfiniteAdelicGL K n` (for a given Borel structure) and
`U` a neighbourhood of `1`. For every `κ : SmoothCompactKernel K n` there are `m` and
`φ ψ : Fin m → SmoothCompactKernel K n` with `tsupport (φ i) ⊆ U`, `tsupport (ψ i) ⊆ tsupport κ` and

`κ g = ∑ i, ∫ y, φ i y * ψ i (y⁻¹ * g) ∂μ` for all `g`.

## Proof

`SmoothCompactKernel K n` consists of the functions on `GL_n(F_∞)` whose transport by
`archimedeanGLCoordinates K n` to `ArchimedeanGL K n = (ArchimedeanMatrix K n)ˣ` is smooth for
Mathlib's manifold structure on the units, and which have compact support. The transport of `κ` is
an element of `smoothCompactKernels (ArchimedeanMatrix K n) (ArchimedeanGL K n)`;
`Langlands.Archimedean.exists_eq_sum_gardingKernelConvolution_units` factors it for the image of
`μ` (a left Haar measure on `ArchimedeanGL K n`, with the Borel structure installed locally), and
the factors and the convolutions are transported back with
`Langlands.Hecke.convolutionIntegral_comp_continuousMulEquiv`.

The file sets `backward.isDefEq.respectTransparency false`, as `Langlands/Global/ArchimedeanGL.lean`
does and for the same reason: resolving the charts on the units of `ArchimedeanMatrix K n` needs
reduction through the normed-ring instances of the operator norm.

## Literature

J. Dixmier and P. Malliavin, *Factorisations de fonctions et de vecteurs indéfiniment
différentiables*, Bull. Sci. Math. (2) 102 (1978), §3, Théorème 3.1; page 6 of the English
translation *Factorizations of infinitely differentiable functions and smooth vectors* (translator
not named, with its own page numbers), where it is Theorem 3.1, proved on pages 6–7. It is stated
there for every real Lie group, of which `GL_n(F_∞)` is one.
