# Determinant density for actual GL Haar measure

This internally derived measure comparison is a prerequisite for the actual
matrix-to-rank-one functional-equation argument. It constructs the GL measure
from additive matrix measure, proves its Haar properties, and compares it with
the existing integral-subgroup-normalized GL Haar measure. It does not prove a
Whittaker Fourier endpoint or the final gamma comparison.

The namespace is `Langlands.RankinSelberg.GLDeterminantDensity`.

## Measures and density

For a field `K`, a natural matrix size `r`, and a multiplicative map with zero
`χ : K →*₀ ℝ≥0`, `matrixWeight r χ X` is `(χ (det X))⁻¹ ^ r`.
Its restriction to the actual unit group is `weight r χ g`. The latter is
implemented through the unit-valued determinant character, so its value is
nonzero, it is multiplicative, and it sends inverses to inverses. When `χ` is
continuous, `weight` is continuous. The ambient `matrixWeight` is measurable
for the Borel matrix space; continuity at singular matrices is not required.

For a Hausdorff topological field, with Borel measurable structures on matrices
and GL, `additiveRestriction r μ` is `μ.comap Units.val`. The underlying-matrix
map is the published open embedding of the actual matrix unit group.
`weightedRestriction r χ μ` is this pulled-back measure with density
`g ↦ (weight r χ g : ℝ≥0∞)`.

`map_withDensity_comp` pushes a pulled-back density through a measurable
embedding, without requiring the density itself to be measurable. Its proof
uses the embedding's restriction and lower-integral formulas.
`map_withDensity_equiv` gives the corresponding inverse-composition formula
for a measurable equivalence.

## Invariance and Haar properties

`additiveRestriction_map_left` proves that if left matrix multiplication by
`g.val` pushes `μ` to `c • μ`, then left group multiplication by `g` pushes
`additiveRestriction r μ` to the same scalar multiple. The proof checks the
image/preimage identity using `g⁻¹` and applies the comap formula on measurable
sets.

`weightedRestriction_leftInvariant` assumes continuous `χ` and the concrete
additive scaling identity

```text
μ.map (X ↦ g.val * X) = weight r χ g • μ
```

for every group element. Transporting the density by left multiplication gives
`weight(g⁻¹ * h) = weight(g)⁻¹ * weight(h)`. Its inverse factor cancels the
factor in the pushed-forward additive measure. Nonzero finite weights justify
the cancellation in `ℝ≥0∞`.

`weightedRestriction_isHaar` additionally assumes local compactness of GL,
finiteness of `μ` on compact sets, and positivity of `μ` on nonempty open sets.
The open embedding transfers compact finiteness and open positivity to the
comap. The continuous nonnegative density gives local finiteness. Since its
value is everywhere nonzero, the density's null-set criterion preserves open
positivity. These facts together with left invariance prove that the weighted
measure is Haar.

`exists_weightedRestriction_eq_smul` additionally assumes second countability
of GL. For any Haar measure `η` on GL it obtains `c : ℝ≥0` with `0 < c` and
`weightedRestriction r χ μ = c • η`. It uses Mathlib's `haarScalarFactor`, its
positivity theorem for two Haar measures, and Haar uniqueness. The scalar is
finite because it belongs to `ℝ≥0`.

## Ambient pushforward and integrals

Let `U` be the range of `Units.val`, the actual invertible matrix locus.
`weightedRestriction_map` proves

```text
(weightedRestriction r χ μ).map Units.val
  = (μ.restrict U).withDensity (X ↦ (matrixWeight r χ X : ℝ≥0∞)).
```

`weightedRestriction_map_ambient` expresses the same measure as
`μ.withDensity (U.indicator (X ↦ (matrixWeight r χ X : ℝ≥0∞)))`.
Neither formula discards the singular locus by an unproved measure-zero claim.
They follow from the density pushforward and `MeasurableEmbedding.map_comap`.

For every function `f` from matrices to a real normed vector space,
`integrable_weightedRestriction_iff` identifies integrability of
`g ↦ f(g.val)` for the weighted GL measure with integrability of
`X ↦ matrixWeight r χ X • f X` for `μ.restrict U`.
`integral_weightedRestriction` equates the corresponding Bochner integrals.
These follow from the measurable embedding's integral and integrability
formulas and Mathlib's nonnegative-density formulas. No continuity or
integrability hypothesis on `f` is needed for the equality of totalized
Bochner integrals; the separate equivalence supplies the convergence statement.

## Actual p-adic normalization

`padic_weightedRestriction_isHaar` treats every prime `p`, algebraic p-adic
field `F`, supplied topological realization `T`, and matrix size `r`, including
zero. For every Borel additive matrix Haar measure `μ`, the measure
`weightedRestriction r T.normalizedAbsHom μ` is Haar. The published
`padicRectangularHaarScaling` with right factor `1` gives exactly the scaling
identity above. Thus the density uses the residue-normalized absolute value,
not the unadjusted spectral norm.

`padic_exists_weightedRestriction_eq_generalLinearHaar` treats every `n : ℕ`
and the actual group `GL_(n+1)`. It installs `T`'s topology, valuative relation,
and local-field structure and proves, for every such additive matrix Haar
measure, existence of a positive finite `c : ℝ≥0` with

```text
weightedRestriction (n+1) T.normalizedAbsHom μ
  = c • generalLinearHaar F.Carrier n.
```

The right side is the Library measure normalized to give the integral GL
subgroup mass one. Second countability follows from the field's supplied
instance and the actual matrix embedding. The additive measure is retained
unchanged throughout; in particular this result applies to the rectangular
product measure constructed from a supplied scalar Haar measure. It makes no
self-dual-measure or character-conductor assumption.

## Provenance

This is an internal derivation from the Library's actual open GL embedding,
residue-normalized rectangular Haar scaling, and normalized GL Haar measure,
together with Mathlib's comap, density, Bochner integral, and Haar uniqueness
results. It does not invoke an original-literature analytic comparison or an
unproved statement about Whittaker functions.
