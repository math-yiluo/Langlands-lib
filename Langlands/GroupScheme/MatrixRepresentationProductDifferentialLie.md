# Lie differentials of actual finite-product matrix representations

Author: Worker 2.

This module proves that the constructed linear differential of an actual
representation of a finite product of general linear group schemes preserves
the pointwise matrix commutator. It bundles the same map as
`Langlands.GroupScheme.MatrixRepresentation.productDifferentialLieHom`
and constructs its Lie action on the full target coordinate module.
All new declarations lie in `Langlands.GroupScheme.MatrixRepresentation`.

## Parameters and standard Lie structures

Let `I : Type u` have a `Finite` instance and `n : I → Type` have
`Fintype` and `DecidableEq` instances in every component. Let
`R : CommRingCat.{u}` be an arbitrary commutative ring, and let
`S : Type u` be a commutative `R`-algebra. The target coordinate
types `m` and `k` lie in universe zero, with `Fintype` and
`DecidableEq` instances.

The source is the actual categorical product
`GeneralLinearProductDualNumber.groupScheme n R`. A representation
`ρ : MatrixRepresentation (groupScheme n R) m` is an actual morphism
of group schemes from this product to the general linear scheme of
coordinate type `m`. Its linear differential is the previously constructed
`ρ.productDifferential S`.

The source Lie algebra is the full dependent family
`∀ i, Matrix (n i) (n i) S` with pointwise matrix bracket
`⁅X,Y⁆ i = X i * Y i - Y i * X i`. The target uses the same
standard associative commutator on matrices. The constructions use
Mathlib's associative Lie structures and `lieEquivMatrix'` for
endomorphisms of the coordinate module.

The index, base and test algebra share universe `u`; matrix coordinates
are in universe zero. Empty products, empty coordinate types and zero
rings are allowed. No characteristic-zero, field, nontriviality, topology
or positive-rank hypothesis is imposed.

## Epsilon matrices and commutators

Write `εA` for the published `GeneralLinear.DualNumber.epsilonMatrix A`,
write `c : S →+* DualNumber S` for the constant inclusion, and
write `dρ` for `ρ.productDifferential`.
`productDifferential_epsilonMatrix` proves

```text
dρ_(DualNumber S) (fun i => ε(X i)) = ε(dρ_S(X)).
```

The family on the left is epsilon times its constant lift, by the
single-factor `epsilonMatrix_eq_smul` in every component.
Linearity of the constructed differential over `DualNumber S` pulls
out this scalar. Its already proved coefficient naturality for
`TrivSqZeroExt.inlAlgHom R S S` identifies its value on the constant
family with the constant lift of `dρ_S(X)`. The same scalar epsilon
formula gives the asserted matrix. No extra differential compatibility
is supplied.

`productDifferential_commutator` proves

```text
dρ_S(fun i => X i * Y i - Y i * X i)
  = dρ_S(X) * dρ_S(Y) - dρ_S(Y) * dρ_S(X).
```

Apply the proved product conjugation covariance over `DualNumber S`,
with group element `fun i => matrixUnit (X i)` and matrix family
`fun i => (Y i).map c`. The published single-factor
`matrixUnit_conjugate_constant` computes each source component as
`(Y i).map c + ε(X i * Y i - Y i * X i)`.
The resulting family equality allows linearity, the epsilon formula
and coefficient naturality to compute the left side.
The actual first-order formula
`productMatrixPointsHom_matrixUnit` sends the group element to
`matrixUnit (dρ_S(X))`; the same single-factor conjugation calculation
computes the target. Cancel the equal constant matrix terms and take
`TrivSqZeroExt.snd` in each entry to recover the displayed identity.
Thus bracket preservation follows from actual dual-number evaluation.

`productDifferential_lie` is this equation in the standard Lie notation.
Its source bracket is the pointwise matrix commutator described above.

## Bundled Lie maps and coordinate action

`productDifferentialLieHom ρ S` has type

```text
(∀ i, Matrix (n i) (n i) S) →ₗ⁅S⁆ Matrix m m S.
```

It retains `ρ.productDifferential S` as its underlying linear map
and uses `productDifferential_lie` as its bracket-preservation proof.
`productDifferentialLieHom_toLinearMap` and
`productDifferentialLieHom_apply` record these definitional equalities.

`productDifferentialLieAction ρ S` has type

```text
(∀ i, Matrix (n i) (n i) S) →ₗ⁅S⁆ Module.End S (m → S).
```

It composes the constructed Lie differential with the inverse of
Mathlib's standard matrix Lie equivalence. Its underlying linear map
is the existing `ρ.productDifferentialAction S`, as recorded by
`productDifferentialLieAction_toLinearMap`. The value formula
`productDifferentialLieAction_apply` is

```text
ρ.productDifferentialLieAction S X v = dρ_S(X) *ᵥ v.
```

This is a Lie homomorphism into endomorphisms of every vector in the
coordinate module. No competing global Lie-module instance on the
plain function type is installed.

`productDifferentialLieHom_proj` proves that differentiating the actual
categorical projection to factor `i` gives `X i`; it is the published
linear projection formula for the same underlying map.
For every actual single-GL representation
`σ : MatrixRepresentation (GeneralLinear.groupScheme m R) k`,
`productDifferentialLieHom_comp` proves

```text
productDifferentialLieHom (ρ ≫ σ) S
  = (σ.differentialLieHom S).comp (ρ.productDifferentialLieHom S).
```

Extensionality reduces this equality to the existing actual point-map
chain rule.

## Internal provenance and remaining work

This is an internal extension of the published single-source
`MatrixRepresentationDifferentialLie` construction using the
`MatrixRepresentationProductDifferential` and
`MatrixRepresentationProductDifferentialConjugation` interfaces.
The first-order constant-conjugation calculation, epsilon scalar
identity and matrix Lie equivalence are reused unchanged. The family
epsilon identity and commutator proof, Lie homomorphism, coordinate
action, projection and chain rule are constructed here. No
external-literature identification is asserted.

A representation-indexed coefficient Lie module, restriction of scalars,
comparison with sheaf or analytic differentiation, compact
differentiation and attachment to automorphic coefficient cochains
remain separate work.
