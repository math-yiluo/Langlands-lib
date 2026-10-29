# Matrix evaluation and conjugation for actual finite-product scheme representations

Author: Worker 2.

This module evaluates actual representations of finite products of general
linear group schemes in invertible matrix coordinates. It proves that the
constructed product differential intertwines conjugation by every matrix
family. The principal definition is
`Langlands.GroupScheme.MatrixRepresentation.productMatrixPointsHom`.

## Parameters and scope of the product

Let `I : Type u` have a `Finite` instance and `n : I → Type` have
`Fintype` and `DecidableEq` instances in every component. Let
`R : CommRingCat.{u}`, and let `S T : Type u` be commutative
`R`-algebras. The output coordinate type `m : Type` also has
`Fintype` and `DecidableEq` instances.

The source is
`GeneralLinearProductDualNumber.groupScheme n R`, the actual categorical
finite product of the general linear schemes of coordinate ranks `n i`.
The representation `ρ` is an actual group-scheme morphism from this product
to `GeneralLinear.groupScheme m R`.

The index type, base and test algebras share universe `u`; coordinate
types lie in universe zero, as in the imported point-coordinate APIs.
Empty products, empty coordinate types and zero rings are allowed.
There is no field, characteristic-zero, topology, nontriviality or
positive-rank hypothesis.

## Actual affine points in matrix-family coordinates

The first declarations lie in
`Langlands.GroupScheme.GeneralLinearProductDualNumber`.
`affineMatrixEquiv S` is a group isomorphism

```text
AffinePoints n R S ≃* ∀ i, GL (n i) S.
```

It composes the published actual product-point isomorphism
`affinePointsPiEquiv S` with the componentwise published
`GeneralLinear.affinePointsEquiv`. It represents every actual product
point and every invertible matrix family; the inverse laws and group laws
come from these isomorphisms.
`affineMatrixEquiv_apply` gives component `i` by taking the actual
categorical projection `x ≫ proj n R i`, then its affine matrix.

For every `f : S →ₐ[R] T`, `affineMatrixEquiv_naturality` identifies
the actual product coefficient map `affineMap f` with entrywise
`GL.map f.toRingHom` in each factor. It follows from naturality of
the product-point equivalence and the single-factor affine comparison.

`affineMatrixEquiv_pointUnit` sends the actual product dual-number point
`pointUnit X` to the family `fun i => DualNumber.matrixUnit (X i)`.
Here and below the prefix `DualNumber.` refers to
`GeneralLinear.DualNumber`, whose `matrixUnit (X i)` is `I + εX_i`.
The proof is the published factorwise `pointUnit_matrix`.
`affineMatrixEquiv_symm_matrixUnit` gives the inverse formula using
injectivity of the constructed group isomorphism.

## Actual evaluated matrix homomorphism

The remaining declarations lie in
`Langlands.GroupScheme.MatrixRepresentation`.
`productMatrixPointsHom ρ S` is a group homomorphism

```text
(∀ i, GL (n i) S) →* GL m S.
```

It first applies the inverse of `affineMatrixEquiv S` to obtain an
actual product-scheme point, then evaluates `ρ.affineMatrix` at that point.
Thus it evaluates the original morphism; no family of unrelated
homomorphisms is supplied. `productMatrixPointsHom_apply` records the
defining composition.

`productMatrixPointsHom_naturality` proves that the value on the
family `fun i => GL.map f.toRingHom (g i)` equals
`GL.map f.toRingHom (ρ.productMatrixPointsHom S g)`.
The proof identifies the inverse coordinate image of the mapped family
with actual spectrum precomposition, by `affineMatrixEquiv_naturality`
and its inverse laws, then applies `ρ.affineMatrix_naturality`.
The algebra map is arbitrary, with no injectivity or invertibility condition.

`productMatrixPointsHom_matrixUnit` is the first-order formula

```text
ρ.productMatrixPointsHom (DualNumber S)
    (fun i => DualNumber.matrixUnit (X i))
  = DualNumber.matrixUnit (ρ.productDifferential S X).
```

It applies the proved inverse coordinate formula, then the existing
actual affine first-order equation of the product differential.

## Conjugation covariance

For every full matrix family `g : ∀ i, GL (n i) S` and
`X : ∀ i, Matrix (n i) (n i) S`,
`productDifferential_conjugate` proves

```text
dρ(fun i => g_i X_i g_i⁻¹) = ρ_S(g) dρ(X) ρ_S(g)⁻¹,
```

where `dρ` is `ρ.productDifferential S`, `ρ_S` is
`ρ.productMatrixPointsHom S`, and all products in the displayed
matrices use the underlying matrices of the units.
This includes every product-group element, without a restriction to
components or infinitesimal elements.

Apply the published single-factor `matrixUnit_conjugate` in every
component to get an equality of actual invertible matrix families over
`DualNumber S`. Apply the actual evaluated product homomorphism to it.
Its homomorphism laws preserve the conjugation product.
Naturality for `TrivSqZeroExt.inlAlgHom R S S` identifies the image
of the constant lift of `g` with the constant lift of `ρ_S(g)`.
The first-order formula identifies the image of the matrix-unit family.
Finally the target single-factor conjugation formula gives equality
of two matrix units, and epsilon coefficient recovery gives the stated
covariance. No conjugation compatibility is assumed.

## Internal provenance and remaining work

This is an internal construction from `MatrixRepresentationProductDifferential`,
`GeneralLinearProductDualNumber`, the published single-factor
`MatrixRepresentationDifferentialConjugation`, and Mathlib's
`MulEquiv.piCongrRight`. Every new coordinate, naturality, first-order
and covariance law is constructed or proved using these interfaces.
No external-literature identification is claimed.

Product bracket preservation and a derived coefficient Lie module,
restriction of scalars, sheaf or analytic differential comparisons,
compact differentiation and attachment to automorphic coefficient
cochains remain separate work.
