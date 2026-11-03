# Degree projections on graded modules and on their tensor products

Author: Worker 1389 designed and implemented this module and wrote this note, as
part of task `90ffbd89-a3dd-4baa-84ba-332896bbbd17` (split unipotence from the
absence of zero Lie weights). No other worker's draft was reused.

The module `Langlands/Algebra/GradedHopf/TensorGrading.lean` is the linear-algebra
layer under the graded Hopf algebra development in
`Langlands/Algebra/GradedHopf/`. Throughout, `k` is a commutative ring, `ι` an index
type with decidable equality, and a module `M` is graded by a family
`ℳ : ι → Submodule k M` carrying Mathlib's `DirectSum.Decomposition ℳ` (so `M` is the
internal direct sum of the `ℳ i`).

## Definitions

- `gradeProj ℳ i : M →ₗ[k] M` is the projection onto the summand of degree `i`:
  `gradeProj ℳ i m = (decompose ℳ m i : M)` (`gradeProj_apply`, which holds by `rfl`).
  It is built as the composite of `decomposeLinearEquiv ℳ`, the `i`-th
  `DirectSum.component` and the inclusion of `ℳ i`.
- `IsGradedMap f`, for a linear map `f : M →ₗ[k] M'` between graded modules, says that
  `f` maps `ℳ i` into `ℳ' i` for every `i`.
- `tensorGrade ℳ 𝒩 n : Submodule k (M ⊗[k] N)` (for `ι` an additive commutative group)
  is the span of the pure tensors `a ⊗ₜ b` with `a ∈ ℳ i`, `b ∈ 𝒩 j` and `i + j = n`:
  the part of total degree `n` of the tensor product grading.
- `tensorProj ℳ 𝒩 n : M ⊗[k] N →ₗ[k] M ⊗[k] N` is the projection onto the part of total
  degree `n`. It decomposes both factors (`TensorProduct.map` of the two
  `decomposeLinearEquiv`), identifies the result with `⨁ (i, j), ℳ i ⊗ 𝒩 j` through
  Mathlib's `TensorProduct.directSum`, and maps the summand `(i, j)` back into
  `M ⊗ N` by `TensorProduct.map` of the two inclusions when `i + j = n`, and by `0`
  otherwise (`DirectSum.toModule`).

These are internal constructions (provenance: internal). They are the standard degree
projections of a graded module and of the tensor product grading `(M ⊗ N)_n =
⊕_{i+j=n} M_i ⊗ N_j`, written out with Mathlib's direct-sum API.

## Lemmas

For `gradeProj`:

- `gradeProj_mem`: the value lies in `ℳ i`;
- `gradeProj_of_mem`: for `m ∈ ℳ j`, `gradeProj ℳ i m = if j = i then m else 0`, with the
  two specialisations `gradeProj_of_mem_self` and `gradeProj_of_mem_ne`;
- `mem_iff_gradeProj`: `m ∈ ℳ i ↔ gradeProj ℳ i m = m`;
- `sum_gradeProj`: `m` is the sum of its components over the support of `decompose ℳ m`;
- `ext_gradeProj`: two elements with equal components are equal;
- `IsGradedMap.comp_gradeProj` and `IsGradedMap.gradeProj_apply`: a graded map commutes
  with the degree projections.

For `tensorGrade` and `tensorProj`:

- `tmul_mem_tensorGrade`: `a ⊗ₜ b ∈ tensorGrade ℳ 𝒩 (i + j)` for `a ∈ ℳ i`, `b ∈ 𝒩 j`;
- `tensorProj_tmul_of_mem`: on such a pure tensor `tensorProj ℳ 𝒩 n` is the identity if
  `i + j = n` and zero otherwise;
- `tensorProj_of_mem_tensorGrade` (with `_self` and `_ne`): on `tensorGrade ℳ 𝒩 m` it is
  the identity if `m = n` and zero otherwise;
- `tensorProduct_induction`: an induction principle on `M ⊗ N` through zero, sums and
  pure tensors of homogeneous elements;
- `tensorProj_mem_tensorGrade` and `mem_tensorGrade_iff`: `tensorProj ℳ 𝒩 n` has image
  in, and is the identity exactly on, `tensorGrade ℳ 𝒩 n`;
- `tensorProj_tmul_of_mem_right` and `tensorProj_tmul_of_mem_left`: if one factor is
  homogeneous of degree `j` (resp. `i`), the projection to total degree `n` projects the
  other factor to degree `n - j` (resp. `n - i`);
- `IsGradedMap.map_tensorGrade` and `IsGradedMap.map_comp_tensorProj`: the tensor product
  `TensorProduct.map f g` of graded maps preserves `tensorGrade` and commutes with
  `tensorProj`.

The proofs reduce to pure tensors of homogeneous elements by `Submodule.span_induction`,
`Decomposition.inductionOn` and `TensorProduct.induction_on`, where the statements follow
from `decompose_of_mem_same`, `decompose_of_mem_ne` and the computation of
`TensorProduct.directSum` on `lof ⊗ₜ lof`.
