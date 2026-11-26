# Compact types and finite level of adelic induced convolution

`Langlands.Global.AdelicGroupPoints.InducedConvolutionCompactDataStatement` fixes a maximal
Iwasawa compact `K`, a kernel `φ` satisfying `IsLeftFiniteTestFunction` for its infinite part
`K_∞`, and a continuous function `v`. It supplies one open subgroup `L` of `G(𝔸_f)` and one
finite-dimensional space `E` of functions `K_∞ → ℂ`. For every complex parameter `λ`, the
convolution `f_λ = hK.inducedConvolution λ φ v` is right `L`-invariant and right `K_∞`-finite,
and every function `k ↦ f_λ(gk)` on `K_∞` belongs to `E`.

## Implemented proof

The convolution integrand is continuous with compact support in the integration variable.
For `k ∈ K`, the twist is trivial in right translation by `k`. The composition law of the
induced translates and left invariance of Haar measure give
`f_λ(gk) = hK.inducedConvolution λ (fun h => φ (k⁻¹h)) v g`.

The open right level is the intersection of the open left level of `φ` with the finite part
of `K`. This finite part is open because `K` is the product of its archimedean and finite
projections and the finite projection of a maximal compact subgroup is open.

The span of the left `K_∞`-translates of `φ` consists of continuous compactly supported
functions. Convolution with a fixed `v` and `λ` is linear in the kernel on this span, and its
image contains all the right `K_∞`-translates of `f_λ`. To bound the compact types uniformly,
the proof takes the coordinate functions of `k ↦ φ(k⁻¹ ·)` in a basis of the kernel span.
The span of these coordinate functions is `E`. Applying the convolution map and evaluating
at `g` expresses `k ↦ f_λ(gk)` as a linear combination of the same coordinate functions.

## Provenance

This is the compact-type and finite-level step in the derivation of
`InducedConvolutionFiniteSpanStatement`. The operator integrates the induced translates
of J. Arthur, *An introduction to the trace formula*, §7, printed p. 33 (PDF p. 45), with the
half-modulus absorbed in the inducing function. The volume is registered as
`arthur-ellwood-kottwitz-2005-harmonic-analysis-shimura`, SHA-256
`88ba9a23fa62e2f62f14af7a5a2a8ffb062be29fc4590bf39c60c173add0a8a7`.
