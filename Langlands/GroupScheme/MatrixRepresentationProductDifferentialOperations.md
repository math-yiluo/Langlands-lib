# Tensor and dual operations on actual finite-product algebraic differentials

Author: Worker 2.

This internal construction extends the published tensor and dual differential
operations to representations of an actual finite categorical product of
general linear group schemes. It proves the first-order matrix rules and
constructs compatible linear endomorphism families on the full algebraic
tensor product and full module dual.

## Parameters and actual source

Let `I : Type u` have a `Finite` instance, and let `n : I → Type` be a
family of finite coordinate types in universe zero, each with `Fintype`
and `DecidableEq` instances. The base is `R : CommRingCat.{u}`, and
`S : Type u` is an arbitrary commutative `R`-algebra. The target coordinate
types `m` and `k` are finite types in universe zero with decidable equality.
The index type, base and test algebra share universe `u`.

Write `P` for `GeneralLinearProductDualNumber.groupScheme n R`. This is
the published categorical finite product of the actual general linear group
schemes `GeneralLinear.groupScheme (n i) R`. The inputs
`ρ : MatrixRepresentation P m` and `σ : MatrixRepresentation P k` are
actual group-scheme morphisms with this common source. Their published
`productDifferential S` maps are constructed by actual postcomposition
on dual-number reduction kernels and recovery of matrix coefficients.
No differential, tensor compatibility or dual compatibility is supplied as
extra input.

The finite product may be empty, every matrix coordinate type may be empty,
and the base and test rings may be zero rings. There is no field,
characteristic, nontriviality, positive-rank or topology hypothesis.
The tensor product is over `S`. The full module dual consists of all
`S`-linear functionals on `m → S`.

## First-order matrix identities

For `X : ∀ i, Matrix (n i) (n i) S`, write `Dρ(X)` for
`ρ.productDifferential S X`. The theorems `productDifferential_tensor`
and `productDifferential_dual` state

```text
D(ρ.tensor σ)(X) = Dρ(X) ⊗ₖ I + I ⊗ₖ Dσ(X),
D(ρ.dual)(X) = -(Dρ(X))ᵀ.
```

Here `ρ.tensor σ` and `ρ.dual` are the published actual tensor and
inverse-transpose group-scheme representations. The proofs use coefficient
recovery for the product differential, the actual affine evaluation formulas
for these representations, and the published first-order image equation
`ρ((I + εX_i)_i) = I + εDρ(X)`.

The imported helper `coefficients_kronecker_matrixUnit` extracts the epsilon
coefficient of `(I + εA) ⊗ₖ (I + εB)`, giving
`A ⊗ₖ I + I ⊗ₖ B`. The imported helper
`coefficients_contragredient_matrixUnit` extracts the coefficient of the
inverse transpose of `I + εA`, giving `-Aᵀ`. Thus both product-source
identities follow from actual evaluation on the product dual-number point.

`productDifferentialAction_toMatrix` proves that the matrix of the
existing coordinate action `ρ.productDifferentialAction S X` is `Dρ(X)`.
It uses the inverse law of Mathlib's matrix-to-linear-map equivalence.

## Full tensor action

`productTensorDifferentialAction ρ σ S` is the constructed `S`-linear map

```text
(∀ i, Matrix (n i) (n i) S)
  →ₗ[S] Module.End S ((m → S) ⊗[S] (k → S)).
```

Its value at `X` is

```text
TensorProduct.map (ρ.productDifferentialAction S X) id
  + TensorProduct.map id (σ.productDifferentialAction S X).
```

Linearity in `X` follows from linearity of the two coordinate differentials
and bilinearity of tensoring linear maps.
`productTensorDifferentialAction_tmul` proves the sum rule

```text
D_tensor(X)(v ⊗ w) = Dρ(X)v ⊗ w + v ⊗ Dσ(X)w.
```

`productTensorDifferentialAction_coordinates` compares this action with
`(ρ.tensor σ).productDifferentialAction S X` through the published
`CoordinateTensor.coordinates S m k` linear equivalence. The equation is
quantified over every tensor. Its proof applies the coordinate formula for
tensoring linear maps, identifies their matrices, and uses the proved
Kronecker-sum differential formula and distributivity of matrix action.
It needs no decomposability assumption.

## Full dual action

`productDualDifferentialAction ρ S` is the constructed `S`-linear map

```text
(∀ i, Matrix (n i) (n i) S)
  →ₗ[S] Module.End S (Module.Dual S (m → S)).
```

It composes `Module.Dual.transpose` with the negative of the existing
coordinate differential action.
`productDualDifferentialAction_apply` proves, for every full linear
functional `f` and every vector `v`,

```text
(productDualDifferentialAction ρ S X f)(v)
  = -f (ρ.productDifferentialAction S X v).
```

The proof uses linearity of `f` at a negative vector.
`productDualDifferentialAction_coordinates` proves equality of linear
functionals after the published coordinate evaluation equivalence
`dotProductEquiv S m`: the differentiated dual scheme action corresponds
to the constructed full dual action. Its coordinate argument `w` is
arbitrary, and the equivalence represents every full linear functional.
The proof applies linear-map extensionality and uses the negative-transpose
matrix identity and the transpose/dot-product identity. The sign therefore
comes from the actual inverse-transpose scheme representation.

## Internal provenance and scope

This is an internal extension of
`MatrixRepresentationDifferentialOperations` using the published
`MatrixRepresentationProductDifferential`. The single-source epsilon
coefficient helpers apply unchanged to the target matrices. The actual
product differential and its first-order image equation replace the
single-source differential throughout. Other ingredients are the published
tensor and dual scheme representations and coordinate equivalences and
Mathlib's tensor, matrix and module-dual operations. No external-literature
identification is asserted.

This unit constructs linear endomorphism families and their coordinate
comparisons. Bundled product Lie actions, restriction-of-scalars
identifications, sheaf or analytic tangent comparisons, compact
differentiation and attachment to automorphic coefficient cochains remain
separate work. It asserts no new cohomology construction.
