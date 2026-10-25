# Dual coefficients of actual group-scheme matrix representations

Author: Worker 2.

This module constructs the dual of an actual finite-coordinate representation
of a group scheme and identifies its affine point action with the full
algebraic module dual. All new declarations are in
`Langlands.GroupScheme.MatrixRepresentation`.

## Parameters and scheme construction

The base is any `R : CommRingCat.{u}`, the source is any group scheme
`G : GroupScheme (Spec R)`, and the coordinate index is any `n : Type`
with `Fintype n` and `DecidableEq n`. For
`ρ : MatrixRepresentation G n`, the definition is the actual composite

```text
dual ρ = ρ ≫ (GeneralLinear.contragredientIso n R).hom.
```

The second factor is the inverse-transpose automorphism of the explicit
general linear group scheme. Thus the dual is again a morphism of group
schemes into the same coordinate general linear group. It is not constructed
by assigning an unrelated action to a group of points.

`dual_dual` proves equality of the twice-dual representation with the
original scheme morphism. This uses associativity and the involutivity of
the contragredient scheme automorphism. For `f : H ⟶ G`, `dual_restrict`
proves that dualization commutes with restriction along `f`, by
associativity of composition.

These are coordinate representations: equality after taking the dual twice
uses the fixed coordinate identification. It is not an assertion that an
arbitrary module is definitionally equal to its algebraic bidual.

## Point matrices and evaluation

For every test scheme `T : Over (Spec R)`, `dual_pointMatrix` identifies
the global-section matrix of `ρ.dual` with the inverse transpose of the
matrix of `ρ`. For every `S : CommAlgCat.{u} R`, `dual_affineMatrix`
proves the same identity over the algebra `S` itself. The proofs apply
the corresponding point formulas for `GeneralLinear.contragredientIso`
to the composite point through `ρ`.

`dual_affineAction` consequently gives the formula

```text
ρ.dual(x)(w) = transpose(ρ(x)⁻¹) * w.
```

All vectors are columns. The inverse is the inverse supplied by the
invertible matrix, not an inverse chosen under a separate nonsingularity
hypothesis. The generic naturality and restriction laws from
`MatrixRepresentation` apply directly to `ρ.dual`, since it is an
actual scheme representation.

`dual_affineAction_pairing` proves

```text
ρ.dual(x)(w) dot ρ(x)(v) = w dot v.
```

The proof uses the inverse-transpose matrix pairing identity. The pairing
is bilinear, `∑ i, w i * v i`; it uses no conjugation.

Mathlib's `dotProductEquiv S n` is an actual linear equivalence

```text
(n → S) ≃ₗ[S] Module.Dual S (n → S).
```

It sends `w` to the functional `v ↦ w dot v`; its inverse evaluates a
functional on each standard basis vector. This equivalence is available
over a commutative ring, including the zero ring and empty coordinate
index. `dual_affineAction_evaluation` proves

```text
dotProductEquiv(ρ.dual(x)(w))(v)
  = dotProductEquiv(w)(ρ(x⁻¹)(v)).
```

The proof expands the matrix action, uses that `affineMatrix` preserves
inverses, and moves the transpose across the dot product.

## Comparison with the full module dual

`affineRepresentation ρ S` forgets invertibility of `affineAction ρ S`,
using `LinearEquiv.automorphismGroup.toLinearMapMonoidHom`, to obtain
Mathlib's representation

```text
Representation S ((algSpec R).obj (op S) ⟶ G.X) (n → S).
```

Its action on vectors is exactly `affineAction`, as recorded by
`affineRepresentation_apply`.

`affineDualEquiv ρ S` is a bundled equivalence of representations from
`ρ.dual.affineRepresentation S` to
`(ρ.affineRepresentation S).dual`. Its underlying linear equivalence is
`dotProductEquiv S n`. The intertwining equation is proved by the
evaluation formula above, using linear-map extensionality twice.
Mathlib's full algebraic dual acts by
`(x · ℓ)(v) = ℓ(ρ(x⁻¹)(v))`, so the inverse in this comparison has the
required direction. `affineDualEquiv_apply` gives the underlying
functional explicitly as the dot product.

This is a comparison with the entire module dual on every affine test
algebra. It imposes no smoothness, continuity, compactness or
finite-dimensional vector-space assumption. The module is finite free
by its coordinate construction.

## Examples, provenance and scope

`dual_trivial` proves that the trivial representation is fixed by duality
as a scheme morphism. The proof uses extensionality on all test-scheme
points, injectivity of the matrix point equivalence and preservation of
the identity matrix by inverse transpose.

`dual_standard` identifies the dual of the standard general linear
representation with the contragredient scheme morphism itself, by the
identity-composition law.

This is internal content derived from `MatrixRepresentation`,
`GeneralLinearContragredient`, Mathlib's coordinate evaluation
equivalence, and Mathlib's full dual representation. The implemented
proofs establish the composition, matrix and evaluation identities
described above. No additional comparison with external literature is
claimed.

The base and affine test algebras share universe `u`, while the finite
index is in `Type`. Arbitrary commutative rings and rank zero are allowed.
This unit does not construct basis-independent algebraic representations
on arbitrary modules, tensor products of scheme representations,
differentiation, or automorphic coefficient attachment.
