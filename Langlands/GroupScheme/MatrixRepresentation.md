# Finite free coefficient representations of group schemes

Author: Worker 2.

This module defines a representation with a chosen finite coordinate basis as
an actual homomorphism of group schemes. It constructs the induced matrix
values on every test scheme and the linear action on affine test algebras.
All declarations are in `Langlands.GroupScheme` or its
`MatrixRepresentation` namespace.

## Parameters and meaning

The base is `Spec R`, where `R : CommRingCat.{u}` is any commutative ring.
The source `G : GroupScheme (Spec R)` is any group scheme over that base.
The coordinate index `n : Type` has `Fintype n` and `DecidableEq n`.
In particular `n = Fin d` gives rank `d`. Empty `n` is permitted; there is
no positive-rank, field, smoothness or reductivity hypothesis.

`MatrixRepresentation G n` abbreviates

```text
G ⟶ GeneralLinear.groupScheme n R.
```

The target is the Library's explicit general linear group scheme, constructed
from matrix and inverse-matrix coordinates. The arrow is a morphism in the
category of group schemes: its underlying scheme morphism preserves the group
law. The representation is therefore more than a chosen action on one group of
points. The phrase “chosen finite coordinate basis” refers to the modules
`n → S` on which its matrices act. This file does not select a basis of a
separately supplied module.

`restrict ρ f`, for `f : H ⟶ G`, is the actual composite `f ≫ ρ`.
`restrict_id` and `restrict_comp` prove the identity and associativity laws
using the category laws.

## Matrix values and coefficient change

For any test scheme `T : Over (Spec R)`, `pointMatrix ρ T` is the group
homomorphism

```text
(T ⟶ G.X) →* GL n Γ(T.left, ⊤).
```

It first composes a point with the underlying morphism of `ρ` using
`pointsMap`, and then applies `GeneralLinear.pointsEquiv`. Thus its value at
`x` is the matrix of `x ≫ ρ.hom.hom`. Both steps are group homomorphisms.
For `a : T' ⟶ T`, `pointMatrix_naturality` identifies the matrix at
`a ≫ x` with entrywise pullback of the matrix at `x` by `a.left.appTop`.
This follows from the proved naturality of `GeneralLinear.pointsEquiv` and
associativity of composition. `pointMatrix_restrict` is the corresponding
composition formula for restriction.

For `S : CommAlgCat.{u} R`, `affineMatrix ρ S` is the group homomorphism
from points on `(algSpec R).obj (op S)` to `GL n S`. It uses the Library's
`GeneralLinear.affinePointsEquiv` to obtain entries in `S` itself.
For an algebra morphism `f : S ⟶ T`, `affineMatrix_naturality` states that
precomposition with `(algSpec R).map f.op` applies `f` to every matrix entry.
`affineMatrix_restrict` again identifies restriction with composition.

`pointMatrix_eq_affineMatrix` compares these two choices of coordinates on an
affine test scheme. The global-section matrix is obtained from the affine
matrix by applying the inverse of `Corepresented.affineSectionsIso S`
entrywise. This is the published comparison for the general linear group,
applied to the composite point. Test algebras and the base ring use the same
arbitrary universe `u`.

## Linear actions

`affineAction ρ S` is a group homomorphism into the group of `S`-linear
automorphisms of `n → S`. Its construction composes `affineMatrix` with
`Matrix.GeneralLinearGroup.toLin` and
`LinearMap.GeneralLinearGroup.generalLinearEquiv`. For a point `x` and a
column vector `v`, the application lemma states

```text
affineAction ρ S x v = affineMatrix ρ S x *ᵥ v.
```

Here the matrix on the right is the underlying matrix of the corresponding
unit. Consequently this action has the usual left matrix-multiplication
convention. `affineAction_naturality` proves that entrywise application of
an algebra morphism intertwines the actions:

```text
ρ_T(Spec(f) ≫ x)(f(v)) = f(ρ_S(x)(v)).
```

The proof uses matrix naturality and the pointwise `RingHom.map_mulVec`
identity. `affineAction_restrict` proves equality of linear automorphisms for
the restricted representation and the original action at the composed point,
by extensionality and `affineMatrix_restrict`.

## Standard and trivial representations

`standard n R` is the identity morphism of the explicit general linear
group scheme. `standard_affineMatrix` recovers its point matrix. In
`standard_affineAction`, a point classified by `g : GL n S` acts on a
vector as `g *ᵥ v`. The proofs reduce identity composition and the inverse
identity for `affinePointsEquiv`.

`trivial G n` is the actual constant identity morphism, formed by composing
the map to the terminal object over `Spec R` with the unit section of the
general linear group scheme. It is bundled as a group-scheme morphism using
`Grp.homMk`. `trivial_pointMatrix` and `trivial_affineMatrix` identify its
values with the identity matrix. Their proofs use the definition of the
identity point, preservation of that point under precomposition, and
preservation of the identity by the relevant group isomorphism.
`trivial_affineAction` then proves that its linear automorphism is the
identity by the matrix-vector identity formula and extensionality.

## Provenance and scope

This is an internal construction from the published
`Langlands.GroupScheme.GeneralLinear` point equivalences, Mathlib's
group-scheme morphisms and `pointsMap`, and Mathlib's matrix-to-linear
automorphism equivalences. Every compatibility is proved by composition,
naturality, or the matrix action formula. No new identification with an
external literature construction is asserted.

The file provides finite free coordinate representations over affine bases.
It does not compare them with representations on arbitrary finite modules,
prove basis independence, differentiate them, construct tensor or dual
representations, classify highest weights, or attach coefficients to an
automorphic realization. Those are separate constructions.
