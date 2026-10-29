# Flat sections of the two-block deformation

Module `Langlands.Representation.RankinSelberg.TwoBlockDeformationFlat`,
namespace `Langlands.RankinSelberg.TwoBlockDeformation`.

This is a helper module for the proof of
`Langlands.RankinSelberg.TwoBlockWhittakerDeformationStatement` (JPSS 1983,
Section (4.5)). It builds the deformation of sections behind conclusions (1)
and (2) of the lemma there. Each section `f` of the undeformed representation
`ρ_0` gets a family `f_u` of sections of the deformed representations `ρ_u`
with `f_0 = f`. One compact open subgroup fixes every `f_u`. The module
contains no Whittaker functionals, integrals or analyticity statements.

## Provenance

JPSS (source ID `jpss-1983-rankin-selberg`, printed pages 408–409) prove
their Lemma (4.5) by citing Casselman–Shalika [C-S, Section 2] and Proposition
(3.2) of [F.S. I], without details. This module supplies the standard
construction those references use: the Iwasawa decomposition
`G = Q̄ K₀` and "flat" sections `f_u(qk) = |det q_1|^u f(qk)`. In the Lean
indexing the first block is block `0`. The construction is derived internal
content. The statements below are exactly what the Lean proves; none of them
is quoted from the source.

## Setting

Let `p` be prime, `F : PadicField.{uF} p`, `T = F.canonicalTopologicalData`,
and give `GeneralLinear (n + 1) F.Carrier` the topology induced by
`T.topology`. In the flat-section part, `h : ∑ i, (m i + 1) = t + 1`,
`B = succBlockShape m h`, `σ i` are complex representations of
`GeneralLinear (m i + 1) F.Carrier` on `W i`, and
`Sections F h (twoBlockDeformedBlocks F m σ u)` is the carrier of
`ρ_u = twoBlockDeformedInduced F m h σ u`, as in
`Langlands.Representation.RankinSelberg.TwoBlockJacquetData`.

## The maximal compact subgroup and the lower Iwasawa decomposition

- `integralOpen F n`: the open subgroup `K₀ = GL_(n+1)(O_F)`. It is defined
  as `Conductor.levelOpenSubgroup F.Carrier n 0` under the canonical
  topology, valuative relation and local-field instances.
- `mem_integralOpen`: `k ∈ K₀` iff all entries of `k` and of `k⁻¹` lie in
  `T.Integers`.
- `isCompact_integralOpen`: `K₀` is compact.
- `inverseTranspose_mem_integralOpen`: `K₀` is stable under `g ↦ (gᵀ)⁻¹`.
- `mem_oppositeParabolic_of_lower`: an invertible matrix with zero entries
  above the diagonal lies in `B.oppositeParabolic` for every block shape `B`.
- `exists_oppositeParabolic_mul`: for every `B : BlockShape (n + 1)` and
  every `g`, there are `q ∈ B.oppositeParabolic F.Carrier` and `k ∈ K₀` with
  `g = q * k`.

  Proof: apply the Library's upper Iwasawa decomposition
  `Iwasawa.exists_mul_upperTriangular` to the inverse transpose `g'` of `g`.
  This gives `k ∈ K₀` with `b = g' k` upper triangular. Then
  `g = (b')(k')⁻¹`, where `b'` is the inverse transpose of `b` and `k'` is
  the inverse transpose of `k`. The matrix `b'` is lower triangular, and
  `(k')⁻¹ ∈ K₀`.

## Block norms

For `B : BlockShape (n + 1)` and a block index `i`:

- `determinantNorm_oppositeLeviProjection_of_mem`: if `r` is in the lower
  parabolic and in `K₀`, then every diagonal block of `r` has determinant of
  normalized absolute value `1`. A private lemma shows this for any matrix
  whose entries and inverse entries are integral: both determinants are
  integral and their absolute values multiply to `1`.
- `oppositeBlockNorm F B i g`: the real number `|det q_i|`. Here `q` is the
  lower-parabolic factor chosen by `exists_oppositeParabolic_mul`, `q_i` is
  its `i`th diagonal block (`B.oppositeLeviProjection`), and `|·|` is
  `T.determinantNorm`.
- `oppositeBlockNorm_eq`: the value is the same for *every* factorization
  `g = q k` with `q` in the lower parabolic and `k ∈ K₀`. Two factors differ
  by an element of the lower parabolic that lies in `K₀`, and the previous
  lemma applies to it.
- `oppositeBlockNorm_pos`: the value is positive.
- `oppositeBlockNorm_mul_integral`: it is unchanged under right
  multiplication by `K₀`.
- `oppositeBlockNorm_oppositeParabolic_mul`: for `q` in the lower parabolic,
  the value at `q g` is `|det q_i|` times the value at `g`.
- `oppositeBlockNorm_oppositeParabolic`: on the lower parabolic it equals
  `|det q_i|`.
- `oppositeBlockNorm_one`: its value at `1` is `1`.
- `isLocallyConstant_oppositeBlockNorm`: it is locally constant, because it
  is right invariant under the open subgroup `K₀`.

For the two-block shape, `blockZeroNorm F h = oppositeBlockNorm F B 0` is the
function `κ(qk) = |det q_0|`. It comes with the specialized lemmas
`blockZeroNorm_pos`, `blockZeroNorm_mul_integral`,
`blockZeroNorm_oppositeParabolic_mul`, `blockZeroNorm_oppositeParabolic`,
`blockZeroNorm_one` and `isLocallyConstant_blockZeroNorm`.

## Flat sections

- `blockTensor_twoBlockDeformedBlocks`: for a Levi element `a`, the block
  tensor of the deformed blocks at parameter `u` is the block tensor at
  parameter `0`, scaled by the scalar
  `T.determinantComplexPower (m 0 + 1) u (a 0) = |det a_0|^u`. The proof
  checks this on pure tensors and uses multilinearity of `tprod`.
- `flatFunction F h σ u f g = (κ(g) : ℂ)^u • f(g)`, for a section `f` of `ρ_0`.
  The power is `Complex.cpow` with a positive real base.
- `flatFunction_covariant`: `flatFunction F h σ u f` satisfies the covariance
  law of `ρ_u` under the lower parabolic. The law of `f` gives the factor
  `δ^(-1/2)(q) (σ_1 ⊗ σ_2)(a)`, the left covariance of `κ` gives
  `|det a_0|^u`, and `|x|^u |y|^u = |xy|^u` holds for nonnegative reals
  (`Complex.mul_cpow_ofReal_nonneg`).
- `flatStabilizer F h σ f`: an open stabilizer of `f`, chosen from smoothness
  of `f`, intersected with `K₀`. Lemmas: `flatStabilizer_le_integralOpen`,
  `sectionEval_mul_flatStabilizer` (`f(xk) = f(x)` on it) and
  `flatFunction_mul_flatStabilizer` (`f_u(xk) = f_u(x)` on it, for every
  `u`).
- `flatSection F h σ u`: the complex-linear map from
  `Sections F h (twoBlockDeformedBlocks F m σ 0)` to
  `Sections F h (twoBlockDeformedBlocks F m σ u)` that sends `f` to the
  smooth section with values `flatFunction F h σ u f` (built with
  `Induction.smoothFunctionOf`).
- `sectionEval_flatSection`: `sectionEval (flatSection F h σ u f) g =
  (blockZeroNorm F h g : ℂ)^u • sectionEval f g`. This holds by definition.
- `flatSection_zero`: `flatSection F h σ 0 f = f`, by `x^0 = 1`.
- `exists_uniform_stabilizer`: for each `f` there is a subgroup `K` of
  `GeneralLinear (t + 1) F.Carrier`, open and compact in the canonical
  topology, such that for **every** `u : ℂ` and `k ∈ K`,
  `inducedRep F h (twoBlockDeformedBlocks F m σ u) k (flatSection F h σ u f)
  = flatSection F h σ u f`. Take `K = flatStabilizer F h σ f`. It is compact
  because it is a closed subgroup (open subgroups are closed) of the compact
  `K₀`.

## Scope

The module does not prove that `u ↦ f_u(g)` is entire, although each value is
an exponential `κ(g)^u` times a fixed vector. It also does not construct
Whittaker functions. Both are left to the modules that use this one.
