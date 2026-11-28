# Kernel vectors paired with continuous square-integrable functions

Module `Langlands.Global.AdelicNormOneKernelVectorUnfolding`.

Notation as in `Langlands.Global.AdelicNormOneKernelVector`: split central data `(T, i, hi, I, e,
hc)` for an affine group scheme `H` over a number field `F`, right invariant Haar measure on
`H(𝔸)¹`, the positive rational quotient `Q = PositiveRationalQuotient F H T i` with projection `q`
and measure `dq = positiveRationalQuotientHaarMeasure F H T i`, `V = L²(Q)`, and
`Θ_h[K](y) = normOnePartialConvolution T i K h y = ∫_{H(𝔸)¹} conj K(n⁻¹ y) h(q n) dn` for any
function `h` on `Q`.

The chosen representative of an `L²` class agrees almost everywhere on
`Q` with the continuous square-integrable function defining the class.
The integrals defining kernel vectors agree for these two functions.

## Results

- `integral_mul_coeFn_toLp`: for a compactly supported continuous `g` on `H(𝔸)` and a continuous
  `f` on `Q` with `f ∈ L²`, `∫_{H(𝔸)} g(a) F(q a) da = ∫_{H(𝔸)} g(a) f(q a) da`, where `F` is the
  representative of the `L²` class of `f`. By the Library's `quotientL2Unfolding` (module
  `Langlands.Analysis.Local.QuotientL2UnfoldingProof`), applied to `conj g`, the left side is the
  `L²` inner product on `Q` of the quotient average of `conj g` with the class of `f`. The
  representatives may then be replaced by the functions themselves (equality almost everywhere on
  `Q`). The result is the integral over `Q` of the quotient average of `a ↦ g(a) f(q a)`, which is
  the right side by the Weil formula of the compatible measures
  (`positiveRationalQuotientHaarMeasure_isCompatible`, field `integral_formula`). The quotient
  average of `g · (f ∘ q)` is `f` times the average of `g`, since `f ∘ q` is invariant under the
  subgroup.
- `integral_normOneSmoothingKernel_mul` takes compactly supported continuous
  kernels `K` on `H(𝔸)` and `ρ` on the positive subgroup. For every function `h`
  on `Q` it gives
  `∫_{H(𝔸)} normOneSmoothingKernel K ρ (a) h(q a) da = (∫ ρ) Θ_h[K](1)`.
  The identity uses Mathlib's Bochner integral, which has value zero on
  nonintegrable integrands. The proof is that of
  `positiveQuotientLpSmoothing_normOneSmoothingKernel` at the point `1`: transport to positive
  and norm-one coordinates (`measurePreserving_normOneDecomposition`), use that positive points
  lie in the subgroup defining `Q`, and separate the product integral.
- `inner_normOneKernelVector_toLp`: for compactly supported continuous `K` and continuous `f ∈ L²(Q)`,
  `⟪normOneKernelVector K, [f]⟫ = Θ_f[K](1)`, with `[f]` the `L²` class of `f` (by
  `normOnePartialConvolution_one_eq_integral` and the two results above).
- `normOnePartialConvolution_eq_inner_toLp`: `Θ_f[K](y) = ⟪normOneKernelVector (rightTranslateCc K y), [f]⟫`
  for every `y ∈ H(𝔸)`.

## Provenance

This is an internal development. It makes the norm-one partial convolutions of continuous
functions in the Iwasawa unfolding of the norm-one Levi pairings of Bernstein–Lapid, *On the
meromorphic continuation of Eisenstein series* (2024), §6.2, (6.8), p. 202, available as inner
products in `L²` of the positive rational quotient.
