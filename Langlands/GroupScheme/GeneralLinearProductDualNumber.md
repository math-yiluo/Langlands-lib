# Dual-number identity kernels of finite products of general linear group schemes

Author: Worker 207.

This module takes the actual categorical finite product of general linear
group schemes and builds dual-number coordinates on the identity kernel of
that product scheme. The main constructions are:

- `pointKernelPiEquiv`, which identifies the actual product kernel with the
  family of the published single-factor kernels;
- `pointKernelEquiv`, which identifies families of matrices
  `∀ i, Matrix (n i) (n i) S` with the actual product kernel. Its bundled
  version `pointKernelMulEquiv` is a group isomorphism;
- `pointKernelMap` and `pointKernelScale`, which restrict coefficient change
  and epsilon scaling of actual product points to the kernel. Their
  coordinate formulas are proved, as is the inverse direction.

Every map, every inverse identity and every compatibility is constructed and
proved here. None of them is a hypothesis. All declarations are in
`Langlands.GroupScheme.GeneralLinearProductDualNumber`. Inside this namespace,
the published single-factor declarations from
`Langlands.GroupScheme.GeneralLinear.DualNumber` are written with the prefix
`DualNumber.`.

## Parameters and conventions

- `I : Type u` with `[Finite I]`.
- `n : I → Type`, with `[Fintype (n i)]` and `[DecidableEq (n i)]` for every
  `i`. Coordinate types live in universe zero, as in the published scheme
  `Langlands.GroupScheme.GeneralLinear.groupScheme`.
- `R : CommRingCat.{u}`.
- Commutative `R`-algebras `S T U : Type u`.

No other hypothesis appears. In particular the following are all allowed: an
empty index type `I`, rank zero (`n i = Fin 0`), and the zero ring as `R` or
`S`. There is also no field, characteristic, topology or nontriviality
assumption, and no supplied compatibility datum.

`groupScheme n R` is the abbreviation

`GroupScheme.pi fun i => GeneralLinear.groupScheme (n i) R`.

This is the published categorical product `∏ᶜ` in group schemes over
`Spec R`, from `Langlands.GroupScheme.Products`. `proj n R i` is the
underlying scheme map of the categorical projection `Pi.π _ i`.
`AffinePoints n R S` abbreviates the morphisms

`(algSpec R).obj (op (CommAlgCat.of R S)) ⟶ (groupScheme n R).X`.

These carry the point-group structure of the actual product group scheme.
`DualNumber S` is Mathlib's `TrivSqZeroExt S S`. The reduction map is
Mathlib's actual first projection `TrivSqZeroExt.fstHom R S S`.

## Internal provenance

This is an internal construction from published Library declarations and
Mathlib. No external mathematical source is used. Its ingredients are:

- `Langlands.GroupScheme.pi`, `piPointsEquiv`, `piPointsEquiv_apply`,
  `piPointsEquiv_symm_π` and `piPointsEquiv_naturality` from
  `Langlands.GroupScheme.Products`. These give the group isomorphism between
  points of the product and families of points of the factors, natural under
  precomposition.
- `Langlands.GroupScheme.GeneralLinear.groupScheme` and `affinePointsEquiv`
  from `Langlands.GroupScheme.GeneralLinear`.
- From `Langlands.GroupScheme.GeneralLinearDualNumber`: `AffinePoints`,
  `affineMap`, `pointReduction`, `PointKernel`, `pointUnit`,
  `pointUnit_matrix`, `matrixUnit`, `coefficients`, `pointKernelEquiv`,
  `pointKernelEquiv_add`, `pointKernelEquiv_naturality`,
  `pointKernelEquiv_scale`, `pointKernelMap`, `pointKernelScale`,
  `coefficientAlgMap`, `epsilonScaleAlg` and `epsilonScale_fst`.
- Mathlib's `TrivSqZeroExt.fstHom`, `Equiv.piCongrRight` and
  `MonoidHom.ker`.

The published `GeneralLinearDualNumber` and `Products` pairs are imported
unchanged.

## Actual product points and reduction

`affineMap f`, for `f : S →ₐ[R] T`, is the group homomorphism that the point
presheaf of the product group scheme assigns to the spectrum map of `f`.
`affineMap_apply` states that its value is actual precomposition with
`(algSpec R).map (CommAlgCat.ofHom f).op`. `affineMap_comp` and
`affineMap_id` follow from functoriality of `algSpec R`.

`affinePointsPiEquiv S` is the published `piPointsEquiv` at the affine test
scheme of `S`. Its `i`th component is `x ≫ proj n R i`
(`affinePointsPiEquiv_apply`, true by definition). The inverse has
projections `x i` (`affinePointsPiEquiv_symm_proj`, from
`piPointsEquiv_symm_π`). `affinePointsPiEquiv_affineMap` evaluates
`piPointsEquiv_naturality` at an index. It shows that product coordinates
turn product coefficient change into the published single-factor
`DualNumber.affineMap` in every factor.

`pointReduction` is `affineMap (TrivSqZeroExt.fstHom R S S)`. This is
reduction of actual product points modulo epsilon, by precomposition with the
spectrum of the dual-number projection. `pointReduction_apply` records that
precomposition, which holds by definition. `PointKernel n R S` is the group
kernel of `pointReduction`. It is a subgroup of the actual product point
group.

## Comparison with the factor kernels

`affinePointsPiEquiv_pointReduction` is `affinePointsPiEquiv_affineMap` for
the projection. It shows that product reduction is the published
`DualNumber.pointReduction` in every factor. `mem_pointKernel_iff` follows:
`affinePointsPiEquiv` is injective and sends `1` to `1`, so a product point
lies in the kernel exactly when each of its factors lies in the corresponding
`DualNumber.PointKernel (n i) R S`.

`pointKernelPiEquiv : PointKernel n R S ≃* ∀ i, DualNumber.PointKernel (n i) R S`
restricts `affinePointsPiEquiv (DualNumber S)` in both directions. Both
membership proofs use `mem_pointKernel_iff`. The inverse identities and
multiplicativity follow from those of `piPointsEquiv`. The `i`th component of
`pointKernelPiEquiv x` has value `x.val ≫ proj n R i`
(`pointKernelPiEquiv_apply_val`). `pointKernelPiEquiv_symm_apply_val`
describes the inverse.

## Matrix coordinates

`pointUnit X`, for `X : ∀ i, Matrix (n i) (n i) S`, is the inverse image
under `affinePointsPiEquiv (DualNumber S)` of the family of published points
`DualNumber.pointUnit (X i)`. `pointUnit_proj` proves that its `i`th scheme
projection is exactly `DualNumber.pointUnit (X i)`. `pointUnit_matrix` proves
that, in published affine coordinates, this projection is the matrix unit
`I + εX_i` (`DualNumber.matrixUnit (X i)`).

`pointKernelEquiv : (∀ i, Matrix (n i) (n i) S) ≃ PointKernel n R S` is
built in two steps. First the published single-factor equivalences
`DualNumber.pointKernelEquiv` are applied componentwise with
`Equiv.piCongrRight`. The result is then composed with the inverse of
`pointKernelPiEquiv`. Its point formulas are:

- `pointKernelEquiv_val`: the underlying point of `pointKernelEquiv X` is
  `pointUnit X`, by definition;
- `pointKernelEquiv_proj`: its `i`th scheme projection is
  `DualNumber.pointUnit (X i)`;
- `pointKernelPiEquiv_pointKernelEquiv`: under `pointKernelPiEquiv`, its
  `i`th component is `DualNumber.pointKernelEquiv (X i)`.

Recovery works through the existing epsilon coefficients.
`pointKernelEquiv_symm_apply` gives component `i` of
`pointKernelEquiv.symm x` as the published inverse
`DualNumber.pointKernelEquiv.symm` applied to the `i`th factor of `x`.
`pointKernelEquiv_symm_coefficients` gives the same component as the matrix
of epsilon coefficients, `DualNumber.coefficients`, of the published affine
matrix of `x.val ≫ proj n R i`. Both hold by definition.

`pointKernelEquiv_add` proves that addition of matrix families is the actual
product group law:

`pointKernelEquiv (X + Y) = pointKernelEquiv X * pointKernelEquiv Y`.

Its proof applies the injective group isomorphism `pointKernelPiEquiv`,
compares component by component, and uses the published
`DualNumber.pointKernelEquiv_add`. The bundled group isomorphism is

`pointKernelMulEquiv : Multiplicative (∀ i, Matrix (n i) (n i) S) ≃* PointKernel n R S`.

Its source multiplication is addition of matrix families, and its
multiplicativity proof is `pointKernelEquiv_add`. The following are derived
consequences:

- `pointKernelEquiv_zero`: zero goes to `1`;
- `pointKernelEquiv_neg`: negation goes to inversion;
- `pointKernelEquiv_symm_mul`, `pointKernelEquiv_symm_one`,
  `pointKernelEquiv_symm_inv`: the same laws for the recovery map;
- `pointUnit_add`: the same law for the underlying points;
- `pointReduction_pointUnit`: `pointUnit X` lies in the actual kernel.

## Coefficient change and epsilon scaling

Two identities between algebra maps prove that reduction is compatible with
the test-algebra maps. Both are checked coefficientwise:

- `fstHom ∘ DualNumber.coefficientAlgMap f = f ∘ fstHom`, by definition of
  the coefficient map;
- `fstHom ∘ DualNumber.epsilonScaleAlg r = fstHom`, by the published
  `DualNumber.epsilonScale_fst`.

`affineMap_comp` turns these into `pointReduction_affineMap` and
`pointReduction_affineMap_scale`.

`pointKernelMap f`, for `f : S →ₐ[R] T`, is precomposition with the spectrum
of `DualNumber.coefficientAlgMap f`. `pointKernelScale r`, for any `r : S`
(including zero and nonunits), is precomposition with the spectrum of
`DualNumber.epsilonScaleAlg r`. Both are group homomorphisms between the
actual product kernels, and the two reduction compatibilities give the kernel
membership. `pointKernelMap_val` and `pointKernelScale_val` record their
values. `pointKernelMap_comp` and `pointKernelMap_id` prove functoriality, via
`affineMap_comp` and coefficientwise identities of the coefficient maps.

`pointKernelPiEquiv_pointKernelMap` and `pointKernelPiEquiv_pointKernelScale`
evaluate `affinePointsPiEquiv_affineMap`. They show that these operations are
the published `DualNumber.pointKernelMap f` and `DualNumber.pointKernelScale r`
in every factor. Combined with the published single-factor laws, they give
the coordinate formulas:

- `pointKernelEquiv_naturality`: `pointKernelMap f (pointKernelEquiv X)` is
  `pointKernelEquiv (fun i => (X i).map f)`, so coefficient change is
  componentwise `Matrix.map f`;
- `pointKernelEquiv_scale`: `pointKernelScale r (pointKernelEquiv X)` is
  `pointKernelEquiv (r • X)`, so epsilon scaling multiplies every component
  by `r`;
- `pointKernelEquiv_symm_naturality` and `pointKernelEquiv_symm_scale`: the
  inverse forms, for every element of the actual product kernel;
- `pointUnit_naturality` and `pointUnit_scale`: the same equations for the
  underlying actual product points.

## Scope

These forward and inverse laws are what a later unit needs to define an
`S`-linear differential for an actual representation of `groupScheme n R` on
a general linear group scheme. In such a representation the actual point map
sends this kernel to the published single-factor kernel. Additivity then comes
from `pointKernelEquiv_add`, `S`-linearity from `pointKernelEquiv_scale` and
`pointKernelEquiv_symm_scale`, and naturality from
`pointKernelEquiv_naturality` and `pointKernelEquiv_symm_naturality`. This
module does not define representation kernel maps or differentials. It also
does not define brackets, analytic or sheaf tangent comparisons, or
archimedean cohomology; those belong to separate work.
