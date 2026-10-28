# Lie differentials of actual algebraic matrix representations

Author: Worker 2.

This module proves bracket preservation for the already constructed algebraic
dual-number differential of an actual general linear group-scheme
representation. It bundles that same linear map as
`Langlands.GroupScheme.MatrixRepresentation.differentialLieHom` and constructs
its Lie action on the target coordinate module.

## Parameters and existing structures

The base is an arbitrary `R : CommRingCat.{u}`. The source and target coordinate
types `n` and `m` are finite types in universe zero with decidable equality. The
representation is an actual group-scheme morphism
`ρ : MatrixRepresentation (GeneralLinear.groupScheme n R) m`. Each test algebra
`S : Type u` is a commutative `R`-algebra. There are no field, characteristic,
nontriviality or positive-rank hypotheses. Empty coordinate types are allowed.
The chain rule also allows an arbitrary finite decidable target type `k` in
universe zero.

The standard matrix Lie bracket is the associative commutator
`[X,Y] = X*Y - Y*X`. The module uses Mathlib's standard associative Lie structures
and its `lieEquivMatrix'` between coordinate endomorphisms and square matrices.
It does not introduce a different matrix bracket. All linear maps and Lie
homomorphisms below are over the test algebra `S` itself.

## Elementary first-order matrix identities

The first three lemmas are in
`Langlands.GroupScheme.GeneralLinear.DualNumber`. Their coordinate type may
instead lie in any universe `v`. Write `c : S →+* DualNumber S` for the constant
inclusion and write `εX` for the existing `epsilonMatrix X`.

`epsilonMatrix_sub` proves `ε(X-Y) = εX - εY` entrywise.
`epsilonMatrix_eq_smul` proves

```text
εX = (DualNumber.eps : DualNumber S) • (X.map c).
```

These two lemmas require neither finiteness nor decidable equality. The latter
identity follows from the actual square-zero multiplication formula
`inr(1) * inl(s) = inr(s)`.

With finiteness and decidable equality, `matrixUnit_conjugate_constant` proves

```text
(matrixUnit X).val * (Y.map c) * (matrixUnit X)⁻¹.val
  = Y.map c + ε(X*Y - Y*X).
```

The left side uses the underlying matrices of actual invertible matrices.
The published `matrixUnit X` is `I + εX`, with inverse `I - εX`. Distribute the
matrix products, apply the published left and right constant/epsilon product
identities and the vanishing product of epsilon matrices, and collect the
additive terms. The order of the commutator is therefore exactly `XY - YX`.

## The differential on epsilon matrices

The remaining declarations are in
`Langlands.GroupScheme.MatrixRepresentation`.
`differential_epsilonMatrix` proves

```text
ρ.differential (DualNumber S) (εX) = ε(ρ.differential S X).
```

First use `epsilonMatrix_eq_smul` and the existing linearity over `DualNumber S`.
Naturality of the actual constructed differential for the constant algebra map
`S →ₐ[R] DualNumber S` identifies its value on `X.map c` with the constant lift
of `ρ.differential S X`. The scalar epsilon identity then gives the result.
This argument uses no additional differential or scalar-compatibility input.

## Commutator and bracket preservation

`differential_commutator` proves for all matrices `X` and `Y`

```text
ρ.differential S (X*Y - Y*X)
  = ρ.differential S X * ρ.differential S Y
      - ρ.differential S Y * ρ.differential S X.
```

Apply the existing `differential_conjugate` over the actual test algebra
`DualNumber S`, with group element `matrixUnit X` and matrix `Y.map c`.
The source conjugation is computed by `matrixUnit_conjugate_constant`.
Linearity, `differential_epsilonMatrix`, and coefficient naturality compute
its differential. On the target side, the actual first-order identity
`matrixPointsHom_matrixUnit` sends the group element to
`matrixUnit (ρ.differential S X)`. The same explicit conjugation identity now
computes the target matrix. Cancel their equal constant matrix terms, compare
entries, and take the actual epsilon coefficient `TrivSqZeroExt.snd`.

`differential_lie` expresses the resulting equation using the standard Lie
bracket notation. No bracket-preservation hypothesis is supplied to either
lemma, and the proof uses no characteristic-zero assumption.

## Bundled Lie maps and coordinate action

`differentialLieHom ρ S` has type

```text
Matrix n n S →ₗ⁅S⁆ Matrix m m S.
```

It retains `ρ.differential S` as its underlying linear map and uses
`differential_lie` for bracket preservation.
`differentialLieHom_toLinearMap` and `differentialLieHom_apply` record these
identifications by definitional equality.

`differentialLieAction ρ S` has type

```text
Matrix n n S →ₗ⁅S⁆ Module.End S (m → S).
```

Compose `differentialLieHom` with the inverse of Mathlib's standard matrix Lie
equivalence. Its underlying linear map is precisely the previously constructed
`ρ.differentialAction S`, as stated by
`differentialLieAction_toLinearMap`. Its value on any coordinate vector is

```text
ρ.differentialLieAction S X v = ρ.differential S X *ᵥ v.
```

The Lie action is given as an endomorphism-valued Lie homomorphism, without
installing competing global Lie-module instances on the plain coordinate
function type.

For any actual `σ : MatrixRepresentation (GeneralLinear.groupScheme m R) k`,
`differentialLieHom_comp` proves equality of bundled Lie homomorphisms

```text
differentialLieHom (ρ ≫ σ) S
  = (σ.differentialLieHom S).comp (ρ.differentialLieHom S).
```

This retains the existing actual point-map chain rule, using extensionality.

## Internal provenance and scope

This is an internal consequence of `MatrixRepresentationDifferential`,
`MatrixRepresentationDifferentialConjugation`, `GeneralLinearDualNumber`,
and Mathlib's matrix and associative Lie structures. All new construction laws
are proved in Lean. No external-literature identification is asserted.

The module constructs the algebraic Lie differential and coordinate Lie action
for actual general linear source schemes over arbitrary commutative bases.
Comparison with sheaf or analytic differentials, products or restrictions of
scalars as source groups, analytic differentiation of the compact action, and
attachment to actual automorphic coefficient cochains remain separate work.
It makes no square-zero or cohomology claim.
