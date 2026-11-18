# Gradings of a Cayley datum from weighted self-dual frames

Author: Worker 118.

This module turns a weighted self-dual basis of a `CayleyDatum K` into a
grading in the sense of
`Langlands.GroupScheme.Composition.CayleyGrading`. It works over every
field `K`, in every characteristic. Here `form` is the polar form `b` of
the norm, and `μ` is the multiplication.

## Definition

`WeightedFrame ι M` (for a finite index type `ι` and an additive group
`M`) consists of:

- frame vectors `vec : ι → CayleyVector K`;
- an involution `dual : ι → ι` (`dual_dual`);
- weights `weight : ι → M`.

It satisfies these conditions:

- `card_eq`: `ι` has eight elements.
- `form_vec`: `b(vec i, vec j)` is `1` if `j = dual i` and `0`
  otherwise.
- `weight_dual`: `weight (dual i) = -weight i`.
- `form_unit`: `b(1, vec i) = 0` whenever `weight i ≠ 0`.
- `form_mul`: `b(vec i · vec j, vec l) = 0` whenever
  `weight i + weight j + weight l ≠ 0`.

## Results

- `coord i z = b(z, vec (dual i))` is the coordinate of `z` along
  `vec i`. Results: `coord_apply`; `dual_injective`; `coord_vec`
  (`coord i (vec j) = δᵢⱼ`); `vec_ne_zero`; `linearIndependent`;
  `span_eq_top` (eight independent vectors in `K⁸`); `sum_coord_smul`
  (`z = ∑ᵢ coord i z • vec i`); `eq_of_coord_eq`.
- `projLin m` is the projection `z ↦ ∑_{weight i = m} coord i z • vec i`.
  Results: `projLin_apply`; `coord_projLin`; `projLin_of_coord` (a
  vector with no coordinates of weight `≠ m` is fixed); `projLin_comp_projLin`
  (orthogonal idempotents); `sum_projLin` (the projections over the
  occurring weights sum to the identity).
- `projLin_mul_vec`: `vec i · vec j` has weight `weight i + weight j`.
  Its coordinate along `vec l` is `b(vec i · vec j, vec (dual l))`, and
  `form_mul` together with `weight (dual l) = -weight l` makes this
  vanish unless `weight l = weight i + weight j`.
- `proj m` is the matrix of `projLin m`, with `proj_mulVec`.
- **`toGrading : c.Grading M`**. The projections are `proj`, and the
  support is the image of `weight`. A weight `m` has a nonzero projection
  exactly when some frame vector has weight `m`, because frame vectors
  are nonzero. The unit has degree `0` by `form_unit`. Products of
  homogeneous vectors are homogeneous by bilinearity and
  `projLin_mul_vec`. `toGrading_support` records the support.

## Provenance

This is internal, derived content. It is an elementary linear-algebra
packaging. The condition `form_mul` is the trilinear form of the
statement that the weights are additive under multiplication. Through
the dual basis, the trilinear form `b(xy, z)` determines the product.
