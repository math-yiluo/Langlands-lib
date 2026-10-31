# Proof of the product-Levi chamber bound

Author: Worker 246.

This module proves

```text
theorem Langlands.glProductLeviChamberCoefficientBound :
    GLProductLeviChamberCoefficientBoundStatement.{uF, uV}
```

for the statement of
[`ProductLeviChamberBoundStatement`](ProductLeviChamberBoundStatement.md).
Auxiliary declarations are in the namespace `Langlands.ProductLeviChamber`. The
general form `chamber_bound` is stated for an arbitrary admissible
representation `ρ` of `C.Levi F.Carrier` on a complex space `V`. The exponent
hypothesis is abbreviated `UpperExponentHypothesis T C ρ`, a verbatim copy of
the hypothesis of the target statement. The final theorem applies it to `S.ρ`.
The proof is a Casselman-style argument with compressed actions on
compact-open fixed vectors. It is not Waldspurger's route through `Ξ`.

## Step 1. Compact open subgroup and compression

The vector `v` is fixed by an open subgroup and the smooth functional `ℓ` by
another. `CuspidalSupport.exists_leviPiOpenSubgroup_subset_forall` (module
`UniformBlockIwahoriBasis`) supplies a product `KP` of compact open subgroups
`K j` inside both. Each `K j` has the block Iwahori factorization for every block
shape of `C.size j`.

The space `W` of `KP`-fixed vectors is finite-dimensional by admissibility. For
an exponent family `lam`, `leviRep T C lam` is the Levi element with blocks
`representative T (lam j)`, and `A(lam)` is the published
`Jacquet.compressedAction` on `W` by this element. The published
`Compact.dual_averageMap_eq_of_mem_fixedVectors` gives
`ℓ(ρ(leviRep lam) v) = φ(A(lam) v₀)`, where `φ` is `ℓ` restricted to `W` and
`v₀` is `v` viewed in `W`.

## Step 2. Eigenvalues of compression by strictly contracting scalars

`norm_eigenvalue_le` is the key estimate. Take any refinement
`D : BlockRefinement C` and nested scalars `c` that are blockwise
`IsStrictlyContracting`. Let `g` be the Levi element with blocks
`(D i).blockScalar (c i)`. Then every eigenvalue `μ` of compression by `g` on
`W` satisfies

```text
‖μ‖ ≤ sqrt (refinedLeviModulus D (z b)),
```

where `b = flatScalars C D c` are the flattened coordinates and
`z = flattenedLeviEquiv ∘ blockScalarLevi`. The proof:

1. If `μ = 0` there is nothing to prove. Otherwise an eigenvector `x` lies in
   every range of the powers of the compression, so it lies in its
   `Jacquet.stableImage`.
2. The published `Jacquet.refinedStableImageJacquetBijective` says that the
   quotient map is bijective from the stable image onto the fixed vectors `Y`
   of the unnormalized Jacquet action of the refined Levi `M`, fixed by
   `KP ∩ M`. Hence `y₀ = mk x ≠ 0`, and `Y` is finite-dimensional.
3. The quotient identity of `Jacquet.refinedUpperCompression` shows that `y₀`
   is a `μ`-eigenvector of the unnormalized action of `g`.
4. Let `π = (T.normalizedRefinedJacquet C D ρ).comp z`, the representation in
   the hypothesis. Each `π b` is the inverse half modulus times the unnormalized
   action of `z b`. Flattened block scalars commute with `M`, so the
   finite-dimensional space `E = Y ⊓ eigenspace(g, μ)` is `π`-invariant and
   nonzero. The operators `π b` commute because the scalar group is
   commutative. `EndomorphismBound.exists_common_eigenvector` gives a common
   eigenvector `w ∈ E`, and `exists_character_of_forall_eigen` gives a
   character `χ` with `π b w = χ b • w`.
5. `χ` is a generalized eigencharacter (`isGeneralizedEigencharacter_of_eigenvector`).
   Its kernel is open: `π` is smooth, by
   `isSmooth_normalizedRefinedJacquet` and the continuity of `z` through
   `flattenedLeviEquivContinuous`, so `w` is fixed by an open subgroup on which
   `χ = 1`.
6. Strict contraction makes the absolute values of `c` monotone within each
   outer block (`monotone_abs_of_isWeaklyContracting`). The hypothesis then
   gives `‖χ b‖ ≤ 1`. Since `z b = g` and `w ∈ E`,
   `χ b = (sqrt modulus)⁻¹ · μ`. This gives the bound.

## Step 3. Fundamental coweights

`FundIndex C` consists of pairs of an outer block `j` and `t < C.size j - 1`;
the corresponding `k = t + 1` satisfies `0 < k < C.size j`. Two auxiliary shapes
are used. `fundRefinement` refines block `j` as `twoBlock (C.size j) k` with
sizes `(k, C.size j - k)`, imported with its coordinate lemma from
[`TwoBlockShape`](../../Group/GL/TwoBlockShape.md), and leaves every other block whole using
`CuspidalSupport.LeviAdmissibility.oneBlock`, imported from
[`OneBlockShape`](../../Group/GL/OneBlockShape.md).
`fundScalars` takes `(ϖ, 1)` in block `j` and `1` elsewhere. Then:

- the scalars are strictly contracting: the ratio in block `j` is
  `|ϖ| = q⁻¹ < 1`, and the other blocks have length one;
- the block scalar element is `leviRep (fundTuple s)`. Here `fundTuple s` is
  `fund (C.size j) k`, the indicator of the coordinates `< k`, in block `j`,
  and `0` elsewhere (`fundScalars_blockScalar`, via `blockScalar_val` and the
  coordinates of `twoBlock`);
- its refined modulus is `q^(-(k (C.size j - k)))`. The other blocks
  contribute `1` and the two-block modulus is computed from
  `determinantNorm_scalar`. This value equals
  `fundWeight s = ∏ j, delta T (fundTuple s j)`, by `degree_fund`:
  the degree of `fund N k` is `k (N - k)`.

`fund_norm_eigenvalue_le` therefore bounds every eigenvalue of `A(fundTuple s)`
by `sqrt (fundWeight s)`. Since `0 < fundWeight s < 1` and `η > 0`, this is
strictly less than `r s = fundWeight s ^ (1/2 - η)`.
`EndomorphismBound.exists_endNorm_pow_le` gives constants `cs s` with
`endNorm (A(fundTuple s) ^ m) ≤ cs s * r s ^ m`.

## Step 4. Multiplicativity and decomposition

For the Borel refinement (singleton blocks), `leviRep lam` is the block scalar
of the uniformizer powers (`borelScalars_blockScalar`). Blockwise antitone
`lam` give weakly contracting scalars. The multiplication law of
`Jacquet.refinedUpperCompression` therefore gives
`A(lam + lam') = A(lam) * A(lam')` for blockwise antitone `lam, lam'`
(`compressedAction_leviRep_add`). Hence `A(m • f) = A(f) ^ m`
(`compressedAction_leviRep_nsmul`, using `compressedAction_one`).

A blockwise normalized family satisfies
`lam = ∑ s, fundCoeff lam s • fundTuple s`, with the successive differences as
coefficients (`normalized_eq_sum_fundTuple`, by telescoping in
`sum_range_telescope` and using that the last coordinate is zero). By
induction over finite sets of indices, with `endNorm_mul_le`,

```text
endNorm (A(lam)) ≤ endNorm (A 0) * ∏ s, cs s * r s ^ fundCoeff lam s.
```

## Step 5. The weights

`delta T` is multiplicative in the exponent tuple (`degree_add`,
`degree_nsmul`). So `∏ j, delta T (lam j) = ∏ s, fundWeight s ^ fundCoeff lam s`
(`prod_delta_eq`). With `Real.rpow_pow_comm` and `Real.finsetProd_rpow`, the
product `∏ s, r s ^ fundCoeff lam s` equals
`∏ j, delta T (lam j) ^ (1/2 - η)`. Combining with Steps 1 and 4 and the bound
`‖φ (f v₀)‖ ≤ Cφ * endNorm f` of `exists_apply_le_endNorm` gives the statement
with `c = Cφ * endNorm (A 0) * ∏ s, cs s`.

## Supporting modules

- [`UniformBlockIwahoriBasis`](../CuspidalSupport/UniformBlockIwahoriBasis.md)
- [`RefinedUpperCompressionProof`](../Jacquet/RefinedUpperCompressionProof.md)
- [`EndomorphismPowerBound`](../../Analysis/EndomorphismPowerBound.md)
