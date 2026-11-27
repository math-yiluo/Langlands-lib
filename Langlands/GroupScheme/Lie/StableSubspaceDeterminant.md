# Determinant characters on stable subspaces of the actual Lie algebra

Let `k` be a field, `G` an affine group scheme over `Spec k` whose structure
morphism is locally of finite type, `l : M ⟶ G` a homomorphism of group schemes
over `Spec k`, and `V` a `k`-subspace of the actual Lie algebra
`Lie(G)(k) = Additive (lieKernel G k)`. This module constructs the rational
character "determinant of `M` acting on `V` through `l` and the adjoint
representation", whenever `V` is stable in the sense below, and computes its
restriction to a commutative group scheme that acts diagonally on a basis of
`V`. All declarations are in the namespace `Langlands.GroupScheme.Lie`.

## Scalar extension of a subspace

For a commutative `k`-algebra `A`, `subspaceExtension G V A : A ⊗[k] V →ₗ[A]
Lie(G)(A)` is the composite of the base change of the inclusion `V ⊆ Lie(G)(k)`
with the Library's scalar-extension isomorphism `kernelScalarExtension G A :
A ⊗[k] Lie(G)(k) ≃ Lie(G)(A)`. On pure tensors it sends `a ⊗ v` to
`a • v_A`, where `v_A` is the image of `v` under the coefficient map
`lieKernelMapLinear G (Algebra.ofId k A)` (`subspaceExtension_tmul`).

- `subspaceExtension_injective`: the map is injective. Base change along the
  flat `k`-module `A` preserves the injectivity of `V ⊆ Lie(G)(k)`
  (`Module.Flat.lTensor_preserves_injective_linearMap`), and
  `kernelScalarExtension` is an isomorphism.
- `subspaceExtension_naturality`: for a `k`-algebra map `f : A → B` the map
  `lieKernelMapLinear G f` on Lie kernels corresponds to `f ⊗ id` on
  `A ⊗[k] V`. The proof checks pure tensors with `lieKernelMapLinear_base`.
- `baseChange_repr_map`: coordinates in the base change `b.baseChange A` of a
  basis `b` of `V` are natural: the coordinates of `(f ⊗ id) x` are the images
  under `f` of those of `x`.

## Stability and the induced operators

`IsAdjointStable G V l` says that for every commutative `k`-algebra `A`, every
`A`-point `m` of `M` and every `x : A ⊗[k] V`, the adjoint operator
`adjoint G A (m ≫ l)` maps `subspaceExtension G V A x` into the range of
`subspaceExtension G V A`. The condition is required after every scalar
extension, including non-reduced algebras, because a rational character is a
morphism of schemes and is determined by its values over all test algebras.

Given `hV : IsAdjointStable G V l`, `stableOperator hV A m` is the
`A`-linear endomorphism of `A ⊗[k] V` obtained by restricting
`adjoint G A (m ≫ l)` to the range of the injective map `subspaceExtension`
and pulling it back along `LinearEquiv.ofInjective`.

- `subspaceExtension_stableOperator`: `subspaceExtension` intertwines
  `stableOperator hV A m` with `adjoint G A (m ≫ l)`.
- `stableOperatorHom hV A` packages the operators as a monoid homomorphism
  from the group of `A`-points of `M`. Multiplicativity follows from the
  intertwining relation, injectivity of `subspaceExtension`, `MonObj.mul_comp`
  and multiplicativity of `adjoint`.
- `stableOperator_naturality`: for a `k`-algebra map `f : A → B`, the operator
  of the image point `affineMap M f m` commutes with `f ⊗ id`. The proof uses
  `adjoint_naturality` and `subspaceExtension_naturality`.

## The rational character

For `A` in `CommAlgCat k`, `stableMatrix hV A` sends an `A`-point `m` of `M` to
the matrix of `stableOperator hV A m` in the basis
`(Module.finBasis k V).baseChange A`, as an invertible matrix
(`MonoidHom.toHomUnits`, since the points form a group). `stableMatrix_apply`
gives its entries, and `stableMatrix_naturality` proves that these matrices
are natural in `A`, from `stableOperator_naturality` and
`baseChange_repr_map`.

Assuming `M.X.left` is affine, `stableDeterminantCharacter hV` is the
restriction of the general-linear determinant character
`GeneralLinear.determinantCharacter` along the algebraic matrix representation
`AffineCoordinates.matrixRepresentationOfAffinePoints M (stableMatrix hV) _`
constructed from these natural matrices.

- `stableDeterminantCharacter_eval` and
  `stableDeterminantCharacter_eval_affine`: its value at a point is the
  determinant of the corresponding matrix (over an affine test, transported to
  global sections by `Corepresented.affineSectionsIso`).
- `stableDeterminantCharacter_affinePoints`: read through
  `Gm.affinePointsEquiv`, the value at an `A`-point `m` is
  `Matrix.GeneralLinearGroup.det (stableMatrix hV A m)`.
- `stableMatrix_det`: this determinant is
  `LinearMap.det (stableOperator hV A m)`. The value of the character is thus
  the basis-free determinant of the induced operator on `A ⊗[k] V`.

## Restriction to a diagonal action

- `rationalCharacters_ext_affine`: two rational characters of an affine
  commutative group scheme `S` over `Spec k` are equal when their values agree
  at every affine point. The proof evaluates at the universal point
  `AffineCoordinates.coordinateCogroupIso`, as the private lemma
  `character_ext_affine` of the module
  `Langlands.GroupScheme.Dynamic.AdjointDeterminantTorusRestrictionProof`
  does.
- `stableOperator_weightBasis`: let `s : S ⟶ M` be a homomorphism from a
  commutative group scheme and `e` a basis of `V` with
  `e j ∈ weightSpace (s ≫ l) (w j)` for characters `w j`. Then for every
  `A`-point `t` of `S`, `stableOperator hV A (t ≫ s)` multiplies the basis
  vector `1 ⊗ e j` by `characterValue (w j) t`. This is the definition of the
  weight space, transported by `subspaceExtension_stableOperator`.
- `det_stableOperator_weightBasis`: for a finite index type, the matrix in the
  basis `e.baseChange A` is diagonal, so the determinant is
  `∏ j, characterValue (w j) t`.
- `characterRestrict_stableDeterminantCharacter`: if `M.X.left` and
  `S.X.left` are affine and the index type is finite, then
  `characterRestrict s (stableDeterminantCharacter hV)` is the sum of the
  characters `w j` (read through
  `rationalCharacters.equivCharacterLattice S`). Both sides take the value
  `∏ j, characterValue (w j) t` at every affine point `t`, by the previous
  results and `comp_groupHom_sum`.

## Provenance

The construction is derived. That the determinant of an algebraic
representation on an invariant subspace is a character is standard linear
algebra over the coordinate ring. The module realizes it with the Library's
interface for building algebraic matrix representations from natural families
of invertible matrices on affine points
(`AffineCoordinates.matrixRepresentationOfAffinePoints`). The adjoint
determinant `adjointDeterminantCharacter` of the module
`Langlands.GroupScheme.Lie.AdjointDeterminantCharacter` is the case of the
whole Lie algebra, built through finite coordinates instead. The module
assumes neither smoothness nor reductivity of `G` or `M`.
