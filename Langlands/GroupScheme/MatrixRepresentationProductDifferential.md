# Linear differentials of representations of finite products of general linear schemes

Author: Worker 2.

This module constructs an algebraic linear differential for every actual
representation of a finite categorical product of general linear group schemes.
The principal definition is
`Langlands.GroupScheme.MatrixRepresentation.productDifferential`.
All new declarations are in `Langlands.GroupScheme.MatrixRepresentation`.

## Parameters and actual source

Let `I : Type u` have a `Finite` instance, and let `n : I → Type` be a
family of coordinate types in universe zero, each with `Fintype` and
`DecidableEq` instances. Let `R : CommRingCat.{u}` be an arbitrary
commutative ring and `S T : Type u` commutative `R`-algebras.
The output coordinate types `m` and `k` are in universe zero with
`Fintype` and `DecidableEq` instances.

Write `P` for
`GeneralLinearProductDualNumber.groupScheme n R`. This is the published
categorical finite product of the actual schemes `GeneralLinear.groupScheme
(n i) R`. The input

```text
ρ : MatrixRepresentation P m
```

is an actual group-scheme morphism from that product to the explicit
general linear group scheme of rank `m`. No map or linearity data is
supplied in addition to this morphism.

The finite index type may be empty, any coordinate type may be empty,
and all base and test rings may be zero rings. There is no field,
characteristic, nontriviality, topology or positive-rank hypothesis.
The index type, base ring and test algebras share universe `u`; all
matrix coordinate types are in universe zero, as in the imported APIs.

`DualNumber S` is `TrivSqZeroExt S S`. The published product coordinates
identify the family `X : ∀ i, Matrix (n i) (n i) S` with an actual
dual-number point `pointUnit X` whose factor `i` is `I + εX_i`.
They identify all such families with the actual kernel of reduction of
product points to `S`-points. The target uses the published single-factor
kernel coordinates from `GeneralLinear.DualNumber`.

## Actual kernel map and linearity

`productDualNumberKernelMap ρ S` is a group homomorphism

```text
GeneralLinearProductDualNumber.PointKernel n R S
  →* GeneralLinear.DualNumber.PointKernel m R S.
```

It sends a point `x` to the actual postcomposition `x.val ≫ ρ.hom.hom`,
as recorded by `productDualNumberKernelMap_val`. Associating the reduction
spectrum map with `x` proves target kernel membership: reduction of `x`
is the identity, and the representation's actual point-group
homomorphism preserves the identity. Multiplication and identity
preservation are those of `pointsMap ρ`.

`productDualNumberKernelMap_naturality` proves that this map commutes
with the product and single-factor coefficient maps for every
`f : S →ₐ[R] T`. `productDualNumberKernelMap_scale` proves the same
compatibility with the actual test-algebra endomorphism `ε ↦ rε`
for every scalar `r : S`, including zero and nonunits. Both proofs
reduce subtype equality to associativity of scheme composition.

`productDifferential ρ S` is the constructed linear map

```text
(∀ i, Matrix (n i) (n i) S) →ₗ[S] Matrix m m S.
```

It applies the product kernel coordinates, then the actual kernel map,
then the inverse single-factor kernel coordinates.
`productDifferential_apply` records this formula. Additivity follows
from addition-to-product for the source coordinates, multiplicativity of
the kernel map, and the inverse target group equivalence.
Scalar compatibility follows from source epsilon scaling, the proved
commutation with the kernel map, and inverse target epsilon scaling.
These laws are proved, rather than assumed of a supplied differential.

## First-order formula and characterization

`productDifferential_kernel` reconstructs exactly the image kernel point.
On underlying points, `productDifferential_pointUnit` says

```text
DualNumber.pointUnit (ρ.productDifferential S X)
  = GeneralLinearProductDualNumber.pointUnit X ≫ ρ.hom.hom.
```

Here the prefix on the left denotes `GeneralLinear.DualNumber`.
Applying the published affine matrix comparison yields
`productDifferential_affineMatrix`:

```text
ρ.affineMatrix (CommAlgCat.of R (DualNumber S)) (pointUnit X)
  = DualNumber.matrixUnit (ρ.productDifferential S X).
```

Thus `ρ((I + εX_i)_i) = I + ε dρ(X)` in actual affine coordinates.
`productDifferential_coefficients` recovers the differential as the
entrywise epsilon coefficients of the actual image matrix.
`productDifferential_eq_iff` characterizes equality to a matrix `Y` by
this first-order equation with `matrixUnit Y` on the right.
Its converse applies epsilon coefficient recovery.
`productDifferential_unique` consequently proves that every linear
map satisfying the equation for all `X` equals the constructed map.

## Naturality, projections and composition

For every `f : S →ₐ[R] T`, `productDifferential_naturality` proves

```text
ρ.productDifferential T (fun i => (X i).map f)
  = (ρ.productDifferential S X).map f.
```

It combines naturality of the product coordinates, the actual kernel map,
and inverse single-factor coordinates. The algebra map need not be
injective or invertible.

`productDifferential_proj` proves that the actual categorical projection
onto factor `i` differentiates to `X ↦ X i`. The proof reconstructs
the target kernel point and uses the published formula `pointUnit_proj`.
`productDifferential_trivial` proves that the actual constant identity
representation has zero differential, by extracting coefficients from
the identity matrix.

For an actual `σ : GL_m → GL_k`, `productDifferential_comp` proves

```text
productDifferential (ρ ≫ σ) S X
  = σ.differential S (ρ.productDifferential S X).
```

Both sides reconstruct the same target kernel point by associativity of
actual scheme composition. `productDifferential_comp_linearMap`
expresses this chain rule as equality of the bundled linear maps.

`productDifferentialAction ρ S` composes the constructed differential
with `Matrix.toLin'`, producing a linear family of endomorphisms of the
full coordinate module `m → S`. `productDifferentialAction_apply`
identifies its value with `ρ.productDifferential S X *ᵥ v`, with the
left column-vector convention. `productDifferentialAction_naturality`
proves that entrywise application of `f` intertwines these families,
using matrix naturality and `RingHom.map_mulVec`.

## Internal provenance and scope

This is an internal construction from the published
`MatrixRepresentationDifferential` and
`GeneralLinearProductDualNumber` interfaces and their dependencies.
The product kernel coordinates, actual categorical projections, addition,
coefficient change and epsilon scaling are reused from the latter.
The single-factor target coordinates and the differential of `σ` are
reused unchanged. The kernel postcomposition, linearity and first-order
proofs adapt the published single-source construction to the actual
product source. Other ingredients are Mathlib's point-group functor,
category associativity, finite matrices and `Matrix.toLin'`.
No external-literature identification is asserted.

This unit constructs linear maps. Product bracket preservation,
conjugation covariance, a derived Lie-module structure, restriction of
scalars, sheaf or analytic tangent comparisons, compact differentiation
and attachment to automorphic coefficient cochains remain separate work.
