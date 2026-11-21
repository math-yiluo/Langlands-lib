# Scalar Harish-Chandra equations on a fixed growth space

This is the continuous scalar realization of the convolution equations used by Bernstein–Lapid,
*On the meromorphic continuation of Eisenstein series*, J. Amer. Math. Soc. 37 (2024), 187–234,
§§3.1–3.3 and 7.2, Lemma 8.3 and equation (8.2a). The source tests an equality of functions.
Here it is tested at every adelic point, using the finite-kernel data of
`AdelicLocalFinitenessStatement` and the fixed-level weighted seminorm topology. This is a
**derived** implementation of those equations, not a proof that an Eisenstein series satisfies
them or of the constant-term equations (8.2b).

## Convolution evaluation

`Langlands.Global.rightConvolutionEvalCLM` takes a continuous, compactly supported kernel `h`
and a point `x ∈ G(𝔸)`. It is the continuous complex-linear form on the Library's
`𝔉^R_L = UniformGrowthFrechetSpace` given by

\[
 v\longmapsto \int_{G(\mathbb A)} h(g)\,v(xg)\,dg.
\]

The Haar measure and the order `xg` are those of the existing `AdelicGroupPoints.rightConvolution`;
`rightConvolutionEvalCLM_apply` identifies the new form with that operator evaluated at `x`.
For this pointwise assertion, the kernel need not be smooth. The proof works for every real
`R` and uses the specified level `L` without any assumption on the level beyond what the
carrier already imposes.

Write `w(g) = ‖g‖^R` for the positive weight in the Library, and `D₁` for
`weightedDerivativeCLM` along the unit of the enveloping algebra. The proof uses:

1. The normalized adelic norm is a positive constant multiple of the continuous matrix
   height (`adelicHeight_eq_scalar_mul_sourceNorm` and `continuous_adelicHeight`). The norm
   is positive because the matrix size is positive. Thus `w` is continuous for any real `R`.
2. `weightedDerivative_one_apply` identifies `D₁(v)(g)` with `v(g) / w(g)`.
   `lp.norm_apply_le_norm` and positivity of `w(g)` give
   `‖v(g)‖ ≤ ‖D₁(v)‖ w(g)`.
3. Continuity of `v` and compact support of `h` give integrability of `h(g) v(xg)`.
   The same compact support gives integrability of `‖h(g)‖ w(xg)`. Taking norms under the
   integral proves `norm_rightConvolution_le`:
   `‖(δ(h)v)(x)‖ ≤ (∫ ‖h(g)‖ w(xg) dg) ‖D₁(v)‖`.
4. Integral additivity and scalar linearity give the underlying linear map. The inequality
   bounds its norm at `v` by a continuous function tending to zero at `v = 0`, since `D₁`
   is continuous. An additive map continuous at zero is continuous everywhere.

## The analytic scalar system

`Langlands.Global.LocalFinitenessData.convolutionEquation` is indexed by pairs `(i, x)` with
`i` in the kernel-family index type and `x ∈ G(𝔸)`. At `s ∈ W` it forms the continuous linear
functional

\[
 v\longmapsto \sum_k b_{ik}(s)\, (\delta(h_{ik})v)(x)-c_i(s)v(x).
\]

For each `i` the sum uses the finite list of fixed kernels from `X`. The zero right-hand
side gives exactly the convolution conjunct of `X.solutions`, by
`mem_systemSolutions_convolutionEquation_iff`. This equivalence uses pointwise testing at
*all* adelic points; no separation theorem is needed.

`isAnalyticSystem_convolutionEquation` proves the Library's `IsAnalyticSystem` for this
family with zero right-hand sides. For fixed `v` and `x` the evaluated convolutions and
`v(x)` are constants in `s`. The holomorphy of `b` and `c` in `IsAdmissible` implies scalar
complex differentiability by testing with the identity form on `ℂ`. Finite sums, products
with constants and subtraction preserve this differentiability. Any other complex-linear
scalar test `m` acts on `z` as `z * m(1)`, which gives precisely the weak holomorphy condition.
