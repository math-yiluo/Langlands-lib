# The Hilbert space of a positive semidefinite kernel

Module `Langlands.Analysis.PositiveKernelHilbert` constructs, for a Hermitian positive
semidefinite kernel `K : ι → ι → ℂ`, a complex Hilbert space with vectors `e i` (`i : ι`) such
that `⟪e i, e j⟫ = K i j` and the span of the `e i` is dense. This is the Kolmogorov
decomposition of a positive definite kernel (equivalently the Moore–Aronszajn reproducing kernel
Hilbert space); the module gives an internal construction from Mathlib's completion of
pre-inner-product spaces, in the same way as Mathlib's GNS construction
(`Mathlib.Analysis.CStarAlgebra.GelfandNaimarkSegal`).

## Declarations

| Declaration | Content |
| --- | --- |
| `kernelForm K f g` | `∑ᵢ ∑ⱼ conj (f i) * g j * K i j` for finitely supported `f g : ι →₀ ℂ` |
| `kernelForm_add_kernel`, `kernelForm_smul_kernel` | linearity in the kernel |
| `kernelForm_inner` | for vectors `v i` and an operator `A`, the form of `⟪A (v i), v j⟫` is `⟪A (∑ f i • v i), ∑ g j • v j⟫` |
| `kernelForm_mapDomain` | change of index along a map `m : ι → ι'` |
| `PositiveKernel ι` | kernel with `conj (K j i) = K i j` and `0 ≤ Re (kernelForm K f f)` for all `f` |
| `PositiveKernel.form`, `form_add_left`, …, `conj_form` | sesquilinearity and conjugate symmetry of the form |
| `PositiveKernel.Pre` | `ι →₀ ℂ` with the semi-inner product `form` (a `PreInnerProductSpace.Core`) |
| `PositiveKernel.Space` | the separated completion of `Pre`, a complex Hilbert space |
| `PositiveKernel.vec i` | the image of `Finsupp.single i 1` |
| `inner_vec_vec` | `⟪vec i, vec j⟫ = K i j` |
| `coe_toPre`, `dense_span_vec` | every finitely supported family maps to `∑ a • vec i`; the span of the `vec i` is dense |
| `ext_inner_vec`, `clm_ext_vec` | vectors (bounded operators) are determined by inner products with (values on) the `vec i` |
| `isometryOfMap`, `isometryOfMap_vec` | an index map `m` with `K' (m i) (m j) = K i j` induces a linear isometry with `vec i ↦ vec (m i)` |
| `opOfMap`, `opOfMap_vec`, `opOfMap_norm_le` | for a real `C ≥ 0` and an index map `m : ι → ι'` with `Re (kernelForm (fun i j => K' (m i) (m j)) f f) ≤ C² Re (K.form f f)` for every finitely supported `f : ι →₀ ℂ` (by `form_mapDomain`, the left side is `Re (K'.form (m_* f) (m_* f))`), a bounded operator `K.Space → K'.Space` with `vec i ↦ vec (m i)` of norm `≤ C` |

## Construction

`Pre` carries the instances `InnerProductSpace.Core.toSeminormedAddCommGroup` and
`InnerProductSpace.ofCore` of the core whose inner product is `form`; its completion
`UniformSpace.Completion Pre` is a Hilbert space (null vectors become zero). Linear maps between
the pre-Hilbert spaces induced by `Finsupp.mapDomain` are extended to the completions by
`ContinuousLinearMap.completion`; for an isometry the extension is isometric by induction on the
completion. The density statement follows from `UniformSpace.Completion.denseRange_coe` and
`coe_toPre`.
