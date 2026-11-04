# Cancelling inverse line characters in a tensor representation

Worker 239, at the request of Worker 706.

This internal helper module collects matrix calculations for finite matrix
representations of group schemes over an arbitrary commutative base ring `R`.
Index types are finite types in `Type` with decidable equality. Every statement
holds on arbitrary scheme tests over `Spec R`; there is no reducedness, field,
smoothness or characteristic assumption. Worker 706 uses these lemmas in the
proof that a normal subgroup of a smooth affine algebraic group over an
algebraically closed field is the kernel of a representation.

## Contents

- `single_mul_single`: over any commutative ring, the pure tensor of the
  standard basis vectors `e_j` and `e_s` is the standard basis vector
  `e_(j,s)` of the product index type.
- `scalarMap_single`: the image of `e_j` under the scalar map into the global
  sections of a test scheme is again `e_j`.
- `tensor_pointMatrix_mulVec_single`: at every point, the tensor
  representation sends `e_(j,s)` to the pure tensor of the images of `e_j` and
  `e_s`. This uses the published Kronecker formula for the tensor
  representation.
- `isFixedVector_tensor_single`: let `i : H ⟶ G` be a homomorphism. Suppose
  that at every point `x` of `H`, there is a unit `a` with the following
  property: `ρ` at `x ≫ i` sends `e_j` to `a • e_j`, and `τ` at `x ≫ i` sends
  `e_s` to `a⁻¹ • e_s`. Then `e_(j,s)` is a fixed vector of the restriction of
  `ρ.tensor τ` along `i`. The two scalars cancel: `a * a⁻¹ = 1`.
- `exists_unit_of_tensor_fixes_single`: if a point `x` of `G` fixes `e_(j,s)`
  under `ρ.tensor τ`, then `ρ` at `x` sends `e_j` to a unit multiple of `e_j`.
  This applies the published lemma `exists_unit_smul_of_pureTensor_eq` (module
  `TensorFixedStabilizer`) to the vectors `e_j` and `e_s`. Their `j` and `s`
  coordinates are both one.
- `mem_range_of_tensor_fixes_single`: assume every point of `G` that preserves
  the line of `e_j` under `ρ` lies in the range of `i`. Then so does every
  point fixing `e_(j,s)` under `ρ.tensor τ`. The fixed-vector equation is
  written in the form of the stabilizer hypothesis of
  `FixedSubrepresentation.range_kernel_eq`.
- `dual_pointMatrix_mulVec_single_of_diagonal`: suppose `σ` at a point `x`
  is the diagonal matrix of units `a t`. Then the dual representation `σ.dual`
  at `x` sends `e_s` to `(a s)⁻¹ • e_s`. The proof uses the published formula
  for the dual: its matrix is the inverse transpose. The inverse of the diagonal
  matrix is the diagonal matrix of inverse units, and the transpose of a
  diagonal matrix is itself.

## Provenance

This module is internal. It formalizes elementary linear-algebra steps used in
Milne, *Algebraic Groups* (2017), Corollary 4.29 (p. 95, PDF p. 111) and
Lemma 5.16 (p. 102, PDF p. 118), which Lemma 5.17 (p. 103, PDF p. 119)
combines.

- The proof of Lemma 5.16 notes that if a subgroup acts on a line through a
  character, it acts on the dual line through the inverse character. The dual
  statement here is the case of a diagonal matrix at one point.
- The proof of Corollary 4.29 tensors Chevalley's line `L^{⊗m}`, on which the
  subgroup acts through `mχ`, with a line `W` on which it acts through `-mχ`.
  The subgroup then acts trivially on the tensor line, and its stabilizer is
  still the subgroup. The tensor statements here are the coordinate form of
  this step for two coordinate lines, with a fixed tensor vector in place of a
  stabilized tensor line: inverse scalars give a fixed tensor, and a point
  fixing the tensor preserves the first line.

The coordinate formulations, the arbitrary base ring and the choice of
statements follow Worker 706's interface request. The module proves no
group-theoretic existence result. It does not choose the lines or the
representations, and it does not prove that a normal subgroup is a kernel.
