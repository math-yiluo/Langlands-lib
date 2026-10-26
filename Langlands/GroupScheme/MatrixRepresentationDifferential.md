# Linear dual-number differentials of general linear scheme representations

Author: Worker 2.

This module constructs an algebraic first-order differential for every actual
group-scheme morphism from a general linear group scheme to another general
linear group scheme. The construction uses its action on actual dual-number
points, and proves linearity using the published coordinates on the identity
kernel. The principal definition is
`Langlands.GroupScheme.MatrixRepresentation.differential`.
All declarations below are in that namespace.

## Parameters and meaning

The base is `R : CommRingCat.{u}`, an arbitrary commutative ring in an explicit
universe. The finite coordinate types `n`, `m`, and, for composition, `k` are
in `Type`, with `Fintype` and `DecidableEq` instances. A representation

```text
ρ : MatrixRepresentation (GeneralLinear.groupScheme n R) m
```

is the published abbreviation for an actual morphism of group schemes
`GL_n → GL_m` over `Spec R`. Its underlying morphism of schemes preserves the
group law. This module places no restriction on how that morphism was
constructed.

The test algebra `S : Type u` is any commutative `R`-algebra; coefficient
change uses another such algebra `T : Type u` and any `R`-algebra map
`f : S →ₐ[R] T`. The base and test algebras share universe `u`, consistently
with the imported scheme-point API. The coordinate types are in universe
zero. Neither rank is assumed positive, and there is no field,
characteristic-zero, nontrivial-ring, smoothness or reductivity assumption.
In particular, empty coordinate types and the zero ring remain allowed.

`DualNumber S` is Mathlib's ring `TrivSqZeroExt S S`, with multiplication
`(a,b)(c,d) = (ac,ad+bc)`. The published
`GeneralLinear.DualNumber.pointKernelEquiv` identifies `Matrix n n S`
with the actual kernel of reduction from `GL_n` points over `DualNumber S`
to points over `S`. Its point is denoted `pointUnit X`, and its affine
matrix is the unit `matrixUnit X = I + εX`.
The reduction is actual precomposition by the spectrum of the first
coefficient projection.

## Maps of actual identity kernels

`dualNumberKernelMap ρ S` is a group homomorphism

```text
PointKernel n R S →* PointKernel m R S.
```

It sends a point `x` to `x.val ≫ ρ.hom.hom`. Membership in the target kernel
follows by associating the reduction spectrum map with `x`, using its kernel
equation, and using preservation of the identity by the induced point-group
homomorphism. Its multiplication and identity laws come from the actual
point-group map `pointsMap ρ`. `dualNumberKernelMap_val` records the
postcomposition formula.

`dualNumberKernelMap_naturality` proves that this homomorphism commutes
with the published `pointKernelMap f`. That map applies the coefficient
change `(a,b) ↦ (f(a),f(b))` by spectrum precomposition.
`dualNumberKernelMap_scale` proves the corresponding statement for
`pointKernelScale r`, which comes from the actual algebra endomorphism
`ε ↦ rε`. Both equalities are associativity of scheme composition after
equality of the kernel subtypes is reduced to equality of their points.
Scaling permits every `r : S`, including zero and nonunits.

## Construction and first-order formulas

`differential ρ S` is an `S`-linear map

```text
Matrix n n S →ₗ[S] Matrix m m S.
```

Its underlying function is

```text
X ↦ pointKernelEquiv.symm
      (dualNumberKernelMap ρ S (pointKernelEquiv X)).
```

`differential_apply` exposes this formula.
Additivity is proved from the published addition-to-kernel-product law,
the multiplicativity of `dualNumberKernelMap`, and the inverse of
`pointKernelMulEquiv`. Scalar compatibility uses
`pointKernelEquiv_scale`, the proved commutation with epsilon scaling,
and `pointKernelEquiv_symm_scale`. No supplied linear map or linearity
hypothesis is part of the construction.

`differential_kernel` is equality in the actual target identity kernel:
mapping the constructed differential back to a point gives exactly the
image of the source point under `ρ`. Taking the underlying points gives
`differential_pointUnit`:

```text
pointUnit (ρ.differential S X) = pointUnit X ≫ ρ.hom.hom.
```

Applying the published affine matrix comparison gives
`differential_affineMatrix`, the first-order identity

```text
ρ.affineMatrix (CommAlgCat.of R (DualNumber S)) (pointUnit X)
  = matrixUnit (ρ.differential S X).
```

Thus the formula is `ρ(I + εX) = I + ε dρ(X)` in actual affine
coordinates. `differential_coefficients` recovers the differential as the
epsilon coefficients of the matrix on the left.

`differential_eq_iff` says that `dρ(X) = Y` is equivalent to the same
first-order identity with `matrixUnit Y` on the right. Its converse applies
the proved coefficient recovery to the matrix equality.
`differential_unique` consequently proves that every `S`-linear map with
that first-order identity for all `X` equals the constructed map.

## Functoriality and coordinate endomorphisms

`differential_naturality` states

```text
ρ.differential T (X.map f) = (ρ.differential S X).map f.
```

It follows from naturality of the source kernel coordinates, the induced
kernel map, and coefficient recovery in the target. The map `f` need not
be injective or invertible.

`differential_standard` proves that the identity scheme representation
has differential `X ↦ X`, using the inverse kernel coordinates and
identity composition. `differential_trivial` proves that the constant
identity representation has differential zero, because its affine matrix
is the identity and its epsilon coefficients vanish.

For `ρ : GL_n → GL_m` and `σ : GL_m → GL_k`,
`differential_comp` proves the chain rule

```text
differential (ρ ≫ σ) S X = σ.differential S (ρ.differential S X).
```

Its proof sends both sides into the actual target kernel, uses
`differential_kernel`, and applies associativity of scheme composition.
`differential_comp_linearMap` gives equality of the corresponding
bundled linear maps.

`differentialAction ρ S` composes the differential with Mathlib's
`Matrix.toLin'` coordinate equivalence, giving a linear map from
`Matrix n n S` to `Module.End S (m → S)`.
`differentialAction_apply` identifies its value on a vector with
`ρ.differential S X *ᵥ v`, using the left column-vector convention.
`differentialAction_naturality` states that entrywise application of `f`
intertwines these endomorphisms, applying the matrix naturality formula
and `RingHom.map_mulVec`.

## Internal provenance and remaining scope

This is an internal construction from the published
`Langlands.GroupScheme.MatrixRepresentation` and
`Langlands.GroupScheme.GeneralLinearDualNumber` modules. In particular,
the actual identity-kernel equivalence, its group law, and its scalar and
coefficient compatibilities are imported from the latter; they are not
assumed anew. The other ingredients are Mathlib's functor of points for
group objects, category associativity, finite matrices, and `Matrix.toLin'`.
Every claimed construction law is proved in Lean. No external-literature
identification is asserted.

The source is the explicit general linear group scheme. Extension to a
general group scheme, products or restrictions of scalars is separate work.
This module constructs linear maps and linear families of endomorphisms;
it does not yet prove preservation of matrix Lie brackets or install a Lie
module structure. Comparison with the sheaf differential
`Langlands.GroupScheme.lieMap`, comparison with analytic tangent spaces,
compact differentiation, and attachment to automorphic relative cochains
also remain separate work.
