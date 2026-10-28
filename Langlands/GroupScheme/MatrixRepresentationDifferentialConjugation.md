# Conjugation covariance of actual algebraic coefficient differentials

Author: Worker 2.

This module evaluates an actual morphism of general linear group schemes on
invertible matrices over each test algebra. It proves naturality and conjugation
covariance of the existing linear dual-number differential. The principal
definition is `Langlands.GroupScheme.MatrixRepresentation.matrixPointsHom`.

## Parameters

The representation has type
`ρ : MatrixRepresentation (GeneralLinear.groupScheme n R) m`, where
`R : CommRingCat.{u}` is an arbitrary commutative ring. The test algebras
`S T : Type u` are commutative `R`-algebras. The finite coordinate types `n`
and `m` lie in `Type`, with `Fintype` and `DecidableEq` instances. No positive
rank, nontrivial-ring, field, or characteristic-zero assumption is needed.
In particular, rank zero is allowed.

The initial matrix calculations are more general: their finite coordinate
type lies in any universe `v`, and they only require a commutative ring `S`.
The two epsilon multiplication lemmas do not need `DecidableEq`; the unit
conjugation lemma uses it for the identity matrix.

## Constant matrices and epsilon matrices

The first three declarations lie in
`Langlands.GroupScheme.GeneralLinear.DualNumber`.
Write `c` for the canonical inclusion `S →+* DualNumber S`, and `εX`
for the published `epsilonMatrix X`.

`constantMatrix_mul_epsilonMatrix` proves

```text
(A.map c) * εX = ε(A * X).
```

`epsilonMatrix_mul_constantMatrix` proves

```text
εX * (A.map c) = ε(X * A).
```

Both use matrix extensionality, the finite sum formula for matrix multiplication,
and the multiplication formulas for constant and epsilon coefficients in
Mathlib's `TrivSqZeroExt S S`. The right multiplication calculation uses the
opposite scalar action, whose value is multiplication on the right.

For `g : GL n S`, `matrixUnit_conjugate` proves the equality of actual units

```text
matrixUnit (g * X * g⁻¹)
  = GL.map c g * matrixUnit X * (GL.map c g)⁻¹.
```

Here the occurrences of `g` in the argument of `matrixUnit` are its underlying
matrices, and `matrixUnit X` is the published unit `I + εX`.
The proof reduces equality of units to equality of matrices, distributes
multiplication, applies the two epsilon multiplication formulas, and uses
`g * g⁻¹ = I`.

## Evaluation and its first-order formula

The remaining declarations lie in
`Langlands.GroupScheme.MatrixRepresentation`.
`matrixPointsHom ρ S` is a monoid homomorphism

```text
GL n S →* GL m S.
```

It first uses the inverse of the published `affinePointsEquiv` to regard
an invertible matrix as an actual affine scheme point, then applies
`ρ.affineMatrix`. Thus the construction evaluates the given scheme morphism;
it does not select an unrelated family of group homomorphisms.
`matrixPointsHom_apply` records this defining composition.

For any `R`-algebra map `f : S →ₐ[R] T`,
`matrixPointsHom_naturality` proves

```text
ρ.matrixPointsHom T (GL.map f.toRingHom g)
  = GL.map f.toRingHom (ρ.matrixPointsHom S g).
```

The proof identifies coefficient change under `affinePointsEquiv` with the
published affine point map, then applies `affineMatrix_naturality`. The map
`f` need not be injective or invertible.

`matrixPointsHom_matrixUnit` restates the existing defining equation of the
constructed linear differential in these matrix coordinates:

```text
ρ.matrixPointsHom (DualNumber S) (matrixUnit X)
  = matrixUnit (ρ.differential S X).
```

## Conjugation covariance

For every `g : GL n S` and `X : Matrix n n S`,
`differential_conjugate` proves

```text
ρ.differential S (g * X * g⁻¹)
  = ρ.matrixPointsHom S g * ρ.differential S X
      * (ρ.matrixPointsHom S g)⁻¹,
```

where the right-hand side and the argument on the left use the underlying
matrices. Apply `matrixPointsHom ρ (DualNumber S)` to
`matrixUnit_conjugate`. Its homomorphism laws preserve the conjugation
product. Naturality for the constant inclusion identifies the image of the
constant lift of `g` with the constant lift of `ρ.matrixPointsHom S g`.
The first-order formula identifies the image of `matrixUnit X`.
The target unit conjugation formula then gives equality of two units of the
form `I + εY`; applying the published epsilon coefficient recovery proves
the displayed equality. No covariance hypothesis is supplied.

## Internal provenance and scope

This is an internal consequence of the published
`MatrixRepresentationDifferential` and `GeneralLinearDualNumber` constructions,
the published natural affine-point comparison for the general linear group
scheme, and Mathlib's matrix and square-zero extension identities. All new
construction laws are proved in Lean. No external-literature identification
is asserted.

The result concerns actual general linear group schemes over a commutative
base ring and their algebraic dual-number differential. Bracket preservation,
a bundled Lie action, comparison with the sheaf or analytic differential,
products or restrictions of scalars as source groups, compact differentiation,
and attachment to automorphic coefficient cochains remain separate work.
