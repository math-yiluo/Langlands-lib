# Tensor and dual operations on actual algebraic differentials

Author: Worker 2.

This internal construction extends the actual dual-number differential of
general linear group-scheme representations. It derives the tensor sum rule
and the negative-transpose dual rule from the published affine matrix formulas.
It constructs linear endomorphism families on the full algebraic tensor product
and full module dual and compares them with the same differentiated scheme
representations through the published coordinate equivalences.

The base is `R : CommRingCat.{u}`, and `S : Type u` is an arbitrary commutative
`R`-algebra. The source and target coordinate types are finite types in universe
zero with decidable equality. Every finite rank, including zero, is allowed.
There is no field, characteristic, topology, nontriviality or supplied
compatibility hypothesis. The full tensor product is over `S`, and the full
module dual means all `S`-linear functionals.

Write `Dρ(X)` for the published constructed `ρ.differential S X`, and let `ρ`
and `σ` be actual representations of the same `GeneralLinear.groupScheme n R`.
The new matrix identities are

```text
D(ρ.tensor σ)(X) = Dρ(X) ⊗ₖ I + I ⊗ₖ Dσ(X),
D(ρ.dual)(X) = -(Dρ(X))ᵀ.
```

The helper `coefficients_kronecker_matrixUnit` extracts the epsilon
coefficient of the Kronecker product of `I + εA` and `I + εB`. Entrywise
dual-number multiplication gives `A ⊗ₖ I + I ⊗ₖ B`. The helper
`coefficients_contragredient_matrixUnit` uses the actual inverse `I - εA` and
transposes it, giving `-Aᵀ`. The proofs of `differential_tensor` and
`differential_dual` apply these helpers to the actual affine point images,
using the published coefficient recovery and first-order image equations.

`differentialAction_toMatrix` states that the matrix of the existing
coordinate differential action is exactly `Dρ(X)`. It follows from the
standard inverse matrix-to-linear-map equivalence.

`tensorDifferentialAction ρ σ S` is the `S`-linear family of endomorphisms of
`(m → S) ⊗[S] (k → S)` defined at `X` by

```text
TensorProduct.map (ρ.differentialAction S X) id
  + TensorProduct.map id (σ.differentialAction S X).
```

Linearity follows from bilinearity of tensoring linear maps.
`tensorDifferentialAction_tmul` proves the sum rule on pure tensors.
`tensorDifferentialAction_coordinates` proves the comparison on every tensor,
using the published `CoordinateTensor.coordinates` equivalence and its
Kronecker matrix formula. No decomposability assumption occurs in this
comparison.

`dualDifferentialAction ρ S` is the `S`-linear family of endomorphisms of
`Module.Dual S (m → S)` obtained by composing `Module.Dual.transpose` with
the negative of the existing differential action. Its action is

```text
(dualDifferentialAction ρ S X f)(v)
  = -f (ρ.differentialAction S X v).
```

The evaluation formula follows from linearity of each functional at a
negative vector.
`dualDifferentialAction_coordinates` proves equality of full linear
functionals after the published `dotProductEquiv S m`: applying this
equivalence to the differentiated dual scheme action equals the constructed
full dual action. The proof uses the negative-transpose matrix identity and
the transpose/dot-product identity. Thus the sign is forced by the actual
inverse-transpose scheme representation.

This is an internal consequence of `MatrixRepresentationDifferential`,
`MatrixRepresentationTensor`, `MatrixRepresentationDual`, the actual
dual-number matrix units, and Mathlib's tensor, matrix and module dual
constructions. No external-literature identification is asserted.
It does not identify the algebraic differential with an analytic or sheaf
differential, construct product or restriction-of-scalars source groups,
differentiate compact actions, or attach these actions to automorphic
cochains. It makes no new bundled Lie-action or cohomology claim.
