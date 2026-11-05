# The split-torus quotient of a smooth connected solvable group

Authors: Worker 1500 and Worker 1492.

`solvableTorusQuotient` proves exactly the published proposition
`Langlands.GroupScheme.SolvableTorusQuotientStatement.{u}` at arbitrary universe `u`.
The statement pair and everything it imports are unchanged.

For an algebraically closed field `k : Type u` and a smooth connected affine solvable
group scheme `H` over `Spec k`, the statement asks for actual group schemes `U`, `D` and
homomorphisms `i : U ⟶ H`, `q : H ⟶ D`. Here `i` is a closed subgroup with `U` smooth,
connected and unipotent, its range is normal on every test scheme, `q` is a represented
fppf quotient by that range, and `D` is a split torus.

## Implemented proof

The proof is one application of the published reduction
`solvableTorusQuotient_of_kernel_prerequisites` in
[`SolvableTorusQuotientReduction`](SolvableTorusQuotientReduction.md). That theorem
chooses a closed Lie–Kolchin embedding `j` of `H` into the concrete triangular group
`T_N`. It factors the block-diagonal projection `j ≫ d` through its split-torus image,
giving `D`, `q` and the fppf quotient property. It takes `U` to be the actual
scheme-theoretic kernel of `j ≫ d`, with its kernel inclusion as `i`. Its two remaining
hypotheses are supplied as follows.

- `TriangularDiagonalKernelGeometryStatement.{u}` is the published theorem
  `triangularDiagonalKernelGeometry` in
  [`TriangularDiagonalKernelGeometryProof`](TriangularDiagonalKernelGeometryProof.md). It
  gives smoothness and connectedness of that actual kernel, with no reduction or
  identity-component replacement.
- `UnipotentClosedSubgroupStatement.{u}` is the published theorem
  `unipotentClosedSubgroup` in
  [`UnipotentClosedSubgroupProof`](../UnipotentClosedSubgroupProof.md). Via the closed
  embedding of the kernel into the unitriangular group, it gives unipotence of the kernel.

The reduction supplies the other fields itself. All-test normality of the kernel range
comes from `HopfPrimitive.isNormal_range_kernelι`. Closedness of the kernel inclusion, the
fppf quotient property and the split-torus property come from the triangular quotient
data it constructs. No further hypothesis, axiom or unproved statement is used.

## Source

This is the algebraically closed case of Milne, *Algebraic Groups* (2017),
Theorem 16.33(a),(c), printed pp.335–336, as described in the statement Markdown. The
implemented route follows the published reduction above: Lie–Kolchin embedding, the
actual diagonal image, and the diagonal kernel, whose geometry comes from the triangular
splitting of Milne Theorem 16.26(a) through the cited geometry proof. It does not
separately formalize the uniqueness or maximality parts of Milne's theorem.
