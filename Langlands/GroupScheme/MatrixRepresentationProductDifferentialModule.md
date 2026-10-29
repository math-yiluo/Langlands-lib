# Actual finite-product algebraic coefficient modules with their derived Lie action

Author: Worker 2.

This module puts the actual point representation and the constructed algebraic
Lie differential of a finite-product general linear scheme representation on
the same finite free coefficient module. Their conjugation covariance follows
from the actual dual-number construction. The principal definition is
`Langlands.GroupScheme.MatrixRepresentation.ProductDifferentialModule`.
All new declarations are in `Langlands.GroupScheme.MatrixRepresentation`.

## Parameters and full coefficient space

Let `I : Type u` have a `Finite` instance and let `n : I → Type`
have `Fintype` and `DecidableEq` instances in every component. Let
`R : CommRingCat.{u}` be an arbitrary commutative ring and let
`S : Type u` be a commutative `R`-algebra. The target coordinate
type `m : Type` has `Fintype` and `DecidableEq` instances.
Write `P` for `GeneralLinearProductDualNumber.groupScheme n R`, and let

```text
ρ : MatrixRepresentation P m.
```

The source `P` is the actual categorical finite product of the general linear
group schemes with coordinate types `n i`. The representation `ρ` is an
actual morphism from that product to `GeneralLinear.groupScheme m R`.
The index, base and test algebra share universe `u`; matrix coordinate types
are in universe zero. Empty products, empty coordinate types and zero rings
are allowed. There is no field, characteristic, nontriviality, topology or
positive-rank hypothesis.

`ρ.ProductDifferentialModule S` is the type synonym `m → S`, indexed
by the actual representation `ρ`. `productDifferentialModuleAddCommGroup`
and `productDifferentialModuleModule` inherit the coordinatewise structures.
`productDifferentialModuleFree` and `productDifferentialModuleFinite`
inherit the usual free and finite module instances.
`productDifferentialModuleCoordinates` is the identity linear equivalence
to `m → S`, so its domain retains every coordinate vector.

The representation index records which derived Lie action is intended.
Different scheme representations therefore act on their own tagged copies
of the coordinate module. The construction supplies explicitly named instances
for the tagged type.

## Derived Lie action

Let `L = ∀ i, Matrix (n i) (n i) S`, with its pointwise associative
commutator bracket, and write `Dρ(X)` for the constructed
`ρ.productDifferential S X`. The product Lie differential constructs
`ρ.productDifferentialLieAction S : L →ₗ⁅S⁆ Module.End S (m → S)`.
Its value sends `v` to `Dρ(X) *ᵥ v`, with the left column-vector
convention. This differential is recovered from the actual dual-number image
of the family `fun i => I + εX_i`; its linearity and bracket preservation
are already proved in the imported product differential interfaces.

`productDifferentialModuleLieRingModule` pulls back the natural action
of the endomorphism Lie algebra on the tagged module along this constructed
Lie homomorphism. It uses `LieRingModule.compLieHom` with the target
endomorphism algebra explicitly specified. Thus the Lie action laws follow
from the constructed differential's bracket preservation.

`productDifferentialModuleLieModule` proves scalar compatibility in
the Lie algebra variable using linearity of `productDifferentialLieAction`,
and in the coefficient vector using linearity of its value.
`productDifferentialModuleCoordinates_lie` states

```text
coordinates(⁅X, v⁆) = Dρ(X) *ᵥ coordinates(v).
```

`productDifferentialModule_toEnd` identifies `LieModule.toEnd` on
the tagged coefficient module, after conjugation by the coordinate equivalence,
with `ρ.productDifferentialLieAction S X`. Both comparisons are
definitional equalities. No candidate differential or covariance hypothesis
is supplied.

## Actual point actions on the same module

The group of actual affine product points is

```text
P(S) = ((algSpec R).obj (op (CommAlgCat.of R S)) ⟶ P.X).
```

`productDifferentialModuleAffineRepresentation` has type
`Representation S P(S) (ρ.ProductDifferentialModule S)`. It is
the existing `ρ.affineRepresentation` on the tagged coefficient type.
`productDifferentialModuleAffineRepresentation_coordinates` identifies
this representation's value with `ρ.affineAction` on every coordinate vector.

The actual product-point equivalence `affineMatrixEquiv S` identifies
`P(S)` with the full group `∀ i, GL (n i) S`.
`productDifferentialModuleRepresentation` composes the same affine-point
representation with its inverse. Thus it is a representation of every
invertible matrix family. If `ρ_S(g)` denotes the actual evaluated
`ρ.productMatrixPointsHom S g`, then
`productDifferentialModuleRepresentation_coordinates` states

```text
coordinates(ρ(g)v) = (ρ_S(g) : Matrix m m S) *ᵥ coordinates(v).
```

Both point-action comparisons are definitional. They evaluate the original
group-scheme morphism in its two existing point descriptions.

## Conjugation covariance

For every full family `g : ∀ i, GL (n i) S`, matrix family `X : L`
and tagged coefficient vector `v`,
`productDifferentialModuleRepresentation_lie` proves

```text
ρ(g) ⁅X, v⁆ = ⁅(fun i => g_i X_i g_i⁻¹), ρ(g)v⁆.
```

The products inside the right bracket use the underlying matrices of the units.
Apply the injective coordinate equivalence and the two coordinate formulas.
The actual product differential's proved conjugation identity computes
`Dρ(fun i => g_i X_i g_i⁻¹)` as
`ρ_S(g) Dρ(X) ρ_S(g)⁻¹`. Matrix associativity and cancellation
of the inverse of `ρ_S(g)` prove the required equality on every vector.
There is no restriction to an identity component or infinitesimal elements.

`productDifferentialModuleAffineRepresentation_lie` proves the same
covariance for every actual affine product point `x`. Its conjugating family
is `affineMatrixEquiv S x`. The proof applies matrix-family covariance
at this family, then uses the inverse law of the point equivalence to recover
the original `x`. Consequently both covariance laws follow from the actual
dual-number calculation.

## Internal provenance and scope

This is an internal extension of the published single-source
`MatrixRepresentationDifferentialModule` construction to the actual finite
product source. It uses `MatrixRepresentationProductDifferentialLie` and
`MatrixRepresentationProductDifferentialConjugation` for the constructed
product differential, matrix-family point equivalence and full conjugation
formula. The general affine-point representation comes from the published
`MatrixRepresentationDual` interface. Mathlib supplies the endomorphism
Lie action, `LieRingModule.compLieHom`, finite free coordinate module
structures and matrix multiplication identities. The representation-indexed
type synonym uses the same type-management pattern as the single-source module.
All new module and covariance laws are proved in Lean. No external-literature
identification is asserted.

This unit constructs algebraic coefficient modules for actual finite products
of general linear schemes. Restriction of scalars, sheaf or analytic
differentiation comparisons, restriction to archimedean compact groups and
attachment to automorphic coefficient cochains remain separate work.
