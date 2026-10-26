# Dual-number coordinates at the identity of the general linear group scheme

Author: Worker 518.

This module identifies finite matrices with the kernel of reduction to the
identity in dual-number points of the published general linear group scheme.
The principal bundled construction is
`Langlands.GroupScheme.GeneralLinear.DualNumber.pointKernelMulEquiv`.
Its underlying equivalence is `pointKernelEquiv`. Both maps and both inverse
identities are constructed and proved here.

All declarations below are in
`Langlands.GroupScheme.GeneralLinear.DualNumber`.

## Parameters and conventions

The matrix calculations use an arbitrary finite index type `n : Type v` with
`[Fintype n] [DecidableEq n]`, and a commutative coefficient ring `S : Type u`.
Coefficient change also permits a commutative ring `T : Type w` in another
universe. The scheme-point portion uses the published scheme's index convention
`n : Type`, a base `R : CommRingCat.{u}`, and commutative `R`-algebras
`S T : Type u`. For an unbundled commutative base ring, take
`R = CommRingCat.of R₀`. Universes `u`, `v`, and `w` are explicit.

There is no nonempty-index or nontrivial-ring hypothesis. In particular
`n = Fin 0` is allowed throughout the scheme-point portion; all finite sums
and matrix identities used in the proofs remain valid in rank zero.

`DualNumber S` is Mathlib's abbreviation for `TrivSqZeroExt S S`. Its elements
have a first (constant) coefficient and a second (epsilon) coefficient, and
its multiplication is

`(a, b) * (c, d) = (a*c, a*d + b*c)`.

Here `ε = TrivSqZeroExt.inr 1`, and `inr s = s • ε`. The implementation uses
these actual definitions, rather than assuming a tangent carrier or a
correspondence with desired laws. `GL n S` is the unit group of the matrix
ring, as in the imported general linear scheme implementation.

## Internal provenance and proof route

This is an internal algebraic construction from the imported definitions; no
external mathematical source is used. Its ingredients are:

- Mathlib `Algebra.DualNumber` and `Algebra.TrivSqZeroExt.Basic`, especially
  `TrivSqZeroExt.inr_mul_inr`, `fstHom`, `map`, and coefficient projections;
- Mathlib finite matrix multiplication and `Matrix.GeneralLinearGroup.map`;
- the published `Langlands.GroupScheme.GeneralLinear.groupScheme`,
  `affinePointsEquiv`, and `affinePointsEquiv_naturality` from
  `Langlands.GroupScheme.GeneralLinear`.

The proofs below perform the square-zero matrix calculation and then transport
it through that proved, published affine-point group isomorphism. Existing
scheme construction and point-comparison results are imported by Lean name.

## The actual matrix kernel

`epsilonMatrix X` has entries `inr (X i j)`. Its zero, addition, and negation
identities follow entrywise from those of `inr`. The proof of
`epsilonMatrix_mul X Y` expands matrix multiplication as a finite sum and uses
`inr_mul_inr` to show every summand is zero. Therefore

`(I + εX)(I + εY) = I + ε(X + Y)`.

This is `one_add_epsilonMatrix_mul`. The definition `matrixUnit X` supplies
`I + εX` as the value and `I - εX` as the inverse of an actual matrix unit.
Both inverse equations follow by distributing products and using the proved
square-zero product identity. `matrixUnit_val` and `matrixUnit_inv_val` record
these two matrices. `matrixUnit_zero` and `matrixUnit_add` prove the identity
and addition-to-multiplication equations in `GL`.

`matrixReduction n S` is the group homomorphism induced by the canonical first
projection `TrivSqZeroExt.fstHom S S S`; `MatrixKernel n S` is its group kernel.
`matrixReduction_matrixUnit` proves that the constructed unit reduces to the
identity. `coefficients g` takes the second coefficient of every entry.

The inverse identities are intrinsic:

- `coefficients_matrixUnit` recovers `X` from `matrixUnit X`, because the
  identity matrix has zero epsilon coefficient;
- `fst_of_mem_kernel` extracts the identity constant coefficients from the
  kernel equation;
- `matrixUnit_coefficients` then recovers every kernel element by equality of
  its first and second coefficients at every matrix entry.

`matrixKernelEquiv : Matrix n n S ≃ MatrixKernel n S` bundles those maps and
inverse identities. `matrixKernelMulEquiv` has source
`Multiplicative (Matrix n n S)`, whose multiplication is matrix addition, and
is a multiplicative equivalence to the kernel. Its multiplicativity proof is
`matrixUnit_add`.

## Scalar multiplication and coefficient change

`coefficientMap f` for a ring homomorphism `f : S →+* T` sends `(a, b)` to
`(f a, f b)`. Its ring laws are proved using the displayed dual-number
multiplication. The projection lemmas, `coefficientMap_inr`, and
`coefficientMap_eps` describe this genuine ring map. `matrixUnit_map` proves
that its entrywise action takes `matrixUnit X` to `matrixUnit (X.map f)`.

`epsilonScale r : DualNumber S →ₐ[S] DualNumber S` is Mathlib's square-zero
extension map induced by the linear map `s ↦ r*s`. It fixes the first
coefficient and multiplies the second by `r`, as proved by
`epsilonScale_fst` and `epsilonScale_snd`. `epsilonScale_eps` gives its value
`r • ε` on epsilon. This works for every `r : S`, including zero and nonunits.
`matrixUnit_scale` proves that applying this algebra map entrywise is exactly
`matrixUnit (r • X)`.

`matrixKernelMap f` and `matrixKernelScale r` restrict these actual group maps
to the reduction kernel. The membership proofs use the first coefficients.
`matrixKernelEquiv_naturality` and `matrixKernelEquiv_scale` state the same
compatibilities for the bundled matrix-kernel correspondence.

## Transport to actual group-scheme points

`AffinePoints n R S` abbreviates the morphisms

`(algSpec R).obj (op (CommAlgCat.of R S)) ⟶ (groupScheme n R).X`.

It carries the existing point-group structure of the actual group scheme.
`affineMap f` is the group homomorphism from its point presheaf; its value is
actual precomposition by `(algSpec R).map (CommAlgCat.ofHom f).op`, as stated
by `affineMap_apply`. `affineMap_matrix` is the published naturality theorem
for `affinePointsEquiv` applied to this map.

`pointUnit X` is the inverse image of `matrixUnit X` under the published
`affinePointsEquiv`. `pointUnit_matrix` identifies its matrix.
`pointReduction` is `affineMap` of the canonical algebra projection
`fstHom R S S`; thus its kernel is defined by reduction of actual scheme
points. `PointKernel n R S` is this group kernel.
`pointReduction_matrix` proves its compatibility with `matrixReduction`,
and `pointReduction_pointUnit` proves that the constructed points lie in the
actual kernel.

`pointKernelComparison` restricts `affinePointsEquiv` to a group isomorphism
between `PointKernel n R S` and `MatrixKernel n S`. Its membership and inverse
membership proofs use `pointReduction_matrix` and the two kernel equations;
its inverse identities and multiplicativity follow from the corresponding
laws of `affinePointsEquiv`.

`pointKernelEquiv` composes `matrixKernelEquiv` with the inverse of that
comparison. `pointKernelMulEquiv` is the same construction as a group
isomorphism from `Multiplicative (Matrix n n S)`. The forward point is
`pointUnit X`, by `pointKernelEquiv_val`. The inverse takes second
coefficients in published affine coordinates, by `pointKernelEquiv_symm`.
`pointUnit_add` and `pointKernelEquiv_add` explicitly identify the actual
scheme-point group law with addition of coefficient matrices.

For `f : S →ₐ[R] T`, `coefficientAlgMap f` equips the constructed coefficient
map with its proved base-algebra compatibility. `epsilonScaleAlg r` restricts
the scalars of `epsilonScale r` to `R`. The theorems
`pointUnit_naturality` and `pointUnit_scale` prove the desired equations using
actual precomposition by their spectrum maps, by applying
`affineMap_matrix` and the matrix calculations.

`pointKernelMap` and `pointKernelScale` restrict these actual point maps to
the kernels; membership follows by writing a kernel element in the proved
coordinates. `pointKernelEquiv_naturality` and `pointKernelEquiv_scale` prove
the compatibilities for the bundled equivalence. The corresponding
`pointKernelEquiv_symm_naturality` and `pointKernelEquiv_symm_scale` give the
recovery equations for every element of the actual scheme-point kernel.

This unit is the algebraic identity-kernel calculation needed for later
representation differentiation. Comparison with a cotangent-sheaf Lie module,
analytic tangent spaces, Lie brackets, differentiation of arbitrary
representations, and archimedean cohomology remain separate work. It does not
redefine the published sheaf differential `Langlands.GroupScheme.lieMap`.
