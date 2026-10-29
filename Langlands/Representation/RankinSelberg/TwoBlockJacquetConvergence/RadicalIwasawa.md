# Lower Iwasawa factorization of the upper radical

Module `Langlands.Representation.RankinSelberg.TwoBlockJacquetConvergence.RadicalIwasawa`,
namespace `Langlands.RankinSelberg.TwoBlockConvergence`.

Author: Worker 886.

This is a helper module for the proof of
`Langlands.RankinSelberg.TwoBlockJacquetConvergenceStatement` (JPSS 1983,
Section (4.6)). It controls the lower Iwasawa factorization `u(x) = q k` of
the upper radical `u(x) = (1 x; 0 1)`. One natural number `d` bounds `x`, both
diagonal blocks of `q` and their inverses, and fixes `|det A| = q_F^d` for the
first block.

## Provenance

The content is internal to this proof. It is the elementary matrix
computation behind the estimates of JPSS (source ID
`jpss-1983-rankin-selberg`), Section 4.6, printed pages 410–411: there the
integrand at `u(x)` is evaluated through the factorization of `u(x)` in
`Q̄ K`. The source does not number this computation. The existence of the
factorization is the published
`TwoBlockDeformation.exists_oppositeParabolic_mul`
(`Langlands.Representation.RankinSelberg.TwoBlockDeformationFlat`).

## Integrality lemmas (section `Integral`, any commutative ring `R`)

- `det_mem_of_forall_mem`: the determinant of a square matrix with entries in
  a subring `S` lies in `S`. The matrix is lifted to `S` and `RingHom.map_det`
  is applied.
- `adjugate_mem_of_forall_mem`: likewise for the entries of the adjugate
  (`RingHom.map_adjugate`).
- `val_eq_det_smul_adjugate_inv`: for `A ∈ GL_r(R)`,
  `A = det(A) · adj(A⁻¹)`. This follows from `A⁻¹ adj(A⁻¹) = det(A⁻¹) · 1` and
  `det(A) det(A⁻¹) = 1`.

## Determinants (section `Determinant`)

- `determinant_oppositeParabolic`: the determinant of an element `q` of the
  lower block parabolic of a block shape `B` is the product of the determinants
  of its diagonal blocks `B.oppositeLeviProjection R q i`. After reindexing by
  `B.indexEquiv`, `q` is block triangular for the reversed order of blocks.
  `Matrix.BlockTriangular.det_fintype` applies, and each diagonal block is
  identified with the Levi block through an explicit bijection of index types.
- `determinant_upperRadical`: `det u(x) = 1`, by
  `Matrix.det_fromBlocks_zero₂₁`.

## The factorization (section `Padic`)

`F` is a `p`-adic field with canonical data `T` (integers `O`, uniformizer
`ϖ`, residue cardinality `q_F`, normalized absolute value `|·|`), and
`B = succBlockShape m h` with blocks of sizes `m 0 + 1` and `m 1 + 1`.

- `normalizedAbs_determinant_eq_one`: `k ∈ GL_(n+1)(O)` (the published
  `integralOpen F n`) has `|det k| = 1`. Both `det k` and `det k⁻¹` are
  integral, and their absolute values multiply to `1`.

`exists_radical_factorization`: for every
`x ∈ Matrix (Fin (m 0 + 1)) (Fin (m 1 + 1)) F` there are `q` in the lower block
parabolic, `k ∈ GL_(t+1)(O)` and `d : ℕ` such that

1. `u(x) = q k`;
2. `x ∈ box F (m 0 + 1) (m 1 + 1) d`, that is, `ϖ^d x` is integral;
3. both diagonal blocks `A` and `D` of `q` are `IsEntryBounded` by `d`, that
   is, `ϖ^d A`, `ϖ^d A⁻¹`, `ϖ^d D` and `ϖ^d D⁻¹` are integral;
4. `determinantNorm A = q_F^d` and `determinantNorm D = q_F^(-d)`.

Proof as implemented. Take `u(x) = q k` from `exists_oppositeParabolic_mul`.
Then `q⁻¹ = k u(-x)` (`upperRadical_neg`), `q = u(x) k⁻¹` and `k = q⁻¹ u(x)`.
The block entries are computed with the published block-sum lemmas
`mul_apply_index`, `sum_mul_radical_*` and `sum_radical_*`, and with the
vanishing of the upper-right block of `q⁻¹` (`mem_oppositeParabolic_iff`):

- `A⁻¹ = k₀₀`, `D = (k⁻¹)₁₁`, `k₀₁ = A⁻¹ x`, hence `x = A k₀₁`;
- `D⁻¹ = (q⁻¹)₁₁ = k₁₀ (-x) + k₁₁`.

So `A⁻¹` and `D` are integral. Hence `|det A⁻¹| ≤ 1`, so `|det A| ≥ 1`, and
`|det A| = q_F^d` with `d = -ord(det A) ≥ 0`. Then `ϖ^d det A` has absolute value
`1`, so it is integral. Therefore `ϖ^d A = (ϖ^d det A) adj(A⁻¹)` is integral
(`val_eq_det_smul_adjugate_inv`), and so is `ϖ^d x = (ϖ^d A) k₀₁`. Then
`ϖ^d A⁻¹` and `ϖ^d D` are integral because `ϖ^d` is. Also
`ϖ^d D⁻¹ = k₁₀ (-(ϖ^d x)) + ϖ^d k₁₁` is integral. Finally,
`det u(x) = 1` and `|det k| = 1`, so `|det A| |det D| = 1` by
`determinant_oppositeParabolic`, which gives `|det D| = q_F^(-d)`.
