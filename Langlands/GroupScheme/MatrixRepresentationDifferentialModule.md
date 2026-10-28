# Actual algebraic coefficient modules with their derived Lie action

Author: Worker 2.

This module puts the actual point representation and the constructed algebraic
Lie differential of a general linear group-scheme representation on the same
finite free coefficient module. Their conjugation covariance is proved from
the published dual-number construction. The principal definition is
`Langlands.GroupScheme.MatrixRepresentation.DifferentialModule`.

## Parameters and coefficient space

Let `R : CommRingCat.{u}` be an arbitrary commutative ring and let
`S : Type u` be a commutative `R`-algebra. Let `n` and `m` be types in
`Type`, each with `Fintype` and `DecidableEq` instances, and let

```text
ρ : MatrixRepresentation (GeneralLinear.groupScheme n R) m.
```

Thus `ρ` is an actual morphism of group schemes from the explicit general
linear group scheme of rank `n` to the one of rank `m`.
There is no field, characteristic, nontrivial-ring or positive-rank hypothesis.
Both coordinate types may have cardinality zero.

`ρ.DifferentialModule S` is the type synonym `m → S`, indexed by `ρ`.
The additive group and `S`-module structures are the coordinatewise ones.
`differentialModuleFree` and `differentialModuleFinite` inherit the standard
free and finite module instances. The linear equivalence
`differentialModuleCoordinates` is the identity on coordinates, so every
vector of the coordinate module is represented.

The type synonym records which representation supplies the Lie action.
It permits different scheme representations to act on their respective copies
of the same coordinate module, without changing the standard matrix action on
plain coordinate functions.

## Derived Lie-module structure

Write `Dρ(X)` for the published `ρ.differential S X`. It is constructed
by evaluating the actual scheme morphism on the dual-number point
`I + εX` and recovering its epsilon coefficient.
The published `differentialLieAction` is the Lie algebra homomorphism
whose endomorphism at `X` is `v ↦ Dρ(X) *ᵥ v`.

`differentialModuleLieRingModule` pulls back the natural action of the
endomorphism Lie algebra on the tagged coefficient module along that
homomorphism. Its target endomorphism space is specified explicitly.
Consequently all Lie ring action laws follow from the already proved
bracket preservation of the actual algebraic differential.
`differentialModuleLieModule` proves the two scalar compatibility laws:
linearity of `differentialLieAction` gives scalar compatibility in `X`,
and linearity of its value gives scalar compatibility in the vector.

`differentialModuleCoordinates_lie` states the defining formula

```text
coordinates(⁅X, v⁆) = Dρ(X) *ᵥ coordinates(v).
```

`differentialModule_toEnd` identifies the endomorphism supplied by
`LieModule.toEnd`, after conjugation by the coordinate equivalence,
with the published `ρ.differentialLieAction S X`. Both comparisons are
definitional equalities. No supplied candidate action or compatibility
hypothesis enters this construction.

## Point representations on the same module

Let `Pₙ(S)` denote the group of actual affine points

```text
(algSpec R).obj (op (CommAlgCat.of R S)) ⟶
  (GeneralLinear.groupScheme n R).X.
```

`differentialModuleAffineRepresentation` is a Mathlib
`Representation S Pₙ(S) (ρ.DifferentialModule S)`. It reuses
`ρ.affineRepresentation`, which evaluates `ρ` on these scheme points
and acts by the resulting invertible matrices.
`differentialModuleAffineRepresentation_coordinates` identifies this action
with `ρ.affineAction` on every coordinate vector.

`differentialModuleRepresentation` is the representation of `GL n S`
obtained by composing that same affine-point representation with the inverse
of the published group equivalence `affinePointsEquiv`.
If `ρ_S(g)` denotes `ρ.matrixPointsHom S g`, its coordinate formula is

```text
coordinates(ρ(g)v) = ρ_S(g) *ᵥ coordinates(v).
```

This is `differentialModuleRepresentation_coordinates`; it is again
definitional. These two group actions therefore evaluate the original scheme
morphism in the two existing point descriptions.

## Conjugation covariance

For every `g : GL n S`, `X : Matrix n n S` and vector `v` in the tagged
coefficient module, `differentialModuleRepresentation_lie` proves

```text
ρ(g) ⁅X, v⁆ = ⁅g X g⁻¹, ρ(g)v⁆,
```

where the product inside the right bracket uses the underlying matrices of
`g` and `g⁻¹`. Apply the injective coordinate equivalence, use the two
coordinate formulas, and apply the published `differential_conjugate`.
Associativity of matrix multiplication and cancellation of the inverse of
`ρ_S(g)` prove the equality on every vector.

`differentialModuleAffineRepresentation_lie` proves the same formula for
each actual affine point `x`, using the matrix
`g = affinePointsEquiv n R (CommAlgCat.of R S) x`. Its proof applies
the matrix-coordinate covariance and then the inverse law of that
group equivalence. Both covariance theorems are consequences of actual
dual-number evaluation; covariance is not assumed.

## Internal provenance and scope

This is an internal construction from the published
`MatrixRepresentationDifferentialLie`,
`MatrixRepresentationDifferentialConjugation` and
`MatrixRepresentationDual` interfaces, and Mathlib's endomorphism Lie action
and pullback construction in `Algebra/Lie/OfAssociative` and
`Algebra/Lie/Basic`. The representation-indexed type synonym follows the
same type-management pattern as Mathlib's `Representation.asModule`.
All new construction laws are proved in Lean. No external-literature
identification is claimed.

The module constructs algebraic coefficient modules for actual general linear
source group schemes. Comparison with an analytic or sheaf differential,
product or restriction-of-scalars source differentiation, restriction to
archimedean compact groups, and attachment to automorphic coefficient
cochains require separate constructions.
