# Actual representations as modules over the free algebra of coefficient operators

Author: Worker 902.

This module is internal infrastructure. It turns an actual matrix representation
`ρ : MatrixRepresentation G n` of a group scheme `G` over a field `k` into a module over one
`k`-algebra that does not depend on `ρ`. After that, Mathlib's module theory applies:
stable subspaces become submodules, intertwining matrices become module maps,
irreducibility becomes simplicity, and "sum of simple subrepresentations" becomes
semisimplicity. It is used to prove Milne's character theorem (Theorem 22.38) in
[`Rational.SplitRepresentationCharacterReduction`](../Rational/SplitRepresentationCharacterReduction.md).
No field-theoretic hypothesis beyond `[Field k]` is used, except that
`exists_linearEquiv_submodule` needs `[IsAffineHom G.X.hom]`, which the coordinate
results it cites require.

## The operator algebra

- `OperatorIndex G` is the type of triples `(A, x, ℓ)`: a test algebra
  `A : CommAlgCat.{u} k`, a point `x` of `G` with values in `A`, and a `k`-linear
  functional `ℓ : A →ₗ[k] k`.
- `OperatorAlgebra G` is `FreeAlgebra k (OperatorIndex G)`.
- `coefficientOperator ρ (A, x, ℓ)` is the `k`-linear map `v ↦ ℓ(ρ(x) v)` on `n → k`.
  Here `v` is extended to `n → A` along `algebraMap k A` (`scalarVector`), `ρ(x)` is
  `ρ.affineMatrix A x`, and `ℓ` is applied to each coordinate.
- `operatorAction ρ` is the `k`-algebra map `OperatorAlgebra G →ₐ[k] Module.End k (n → k)`
  given by `FreeAlgebra.lift` of the coefficient operators.
- `OperatorModule ρ` is a type synonym for `n → k`. It carries the `k`-module structure of
  `n → k`, is finite-dimensional, and is a module over `OperatorAlgebra G` through
  `operatorAction ρ`. `k` and the operator algebra form a scalar tower on it.
  `toModule ρ : (n → k) ≃ₗ[k] OperatorModule ρ` is the identity, used as an explicit
  cast; `smul_toModule` and `ι_smul_toModule` compute the action.

## Stable subspaces and intertwiners

- `isStableSubspace_iff_coefficientOperator`: `ρ.IsStableSubspace V` holds exactly when
  `V` is preserved by every coefficient operator. Both are the same quantifier over test
  algebras, points and functionals.
- `IsStableSubspace.operatorAction_mem`: a stable subspace is preserved by the whole
  operator algebra (induction over `FreeAlgebra`).
- `IsStableSubspace.toSubmodule` and `coordinateSubspace` are inverse to each other
  (`coordinateSubspace_toSubmodule`, `toSubmodule_coordinateSubspace`). So stable
  subspaces of `n → k` correspond to submodules of `OperatorModule ρ`.
- `operatorAction_comm_of_coefficientOperator` and `moduleMapOfComm`: a `k`-linear map
  that commutes with every coefficient operator commutes with the whole operator algebra,
  so it is a module map. `coordinateMap` goes back from module maps to `k`-linear maps,
  and `coordinateMap_comm` says the result commutes with every coefficient operator.
- `vector_ext_of_functionals`: two vectors `a b : m → A` with
  `ℓ (a i) = ℓ (b i)` for every `k`-linear functional `ℓ` on `A` are equal (Mathlib's
  `Module.forall_dual_apply_eq_zero_iff`).
- `intertwines_iff_coefficientOperator`: a constant matrix `C` satisfies
  `Intertwines ρ σ C` exactly when `C` commutes with every coefficient operator. The
  forward direction is the Library lemma `Intertwines.linearFunctional_mulVec`. For the
  converse, the matrix identity `C · ρ(x) = σ(x) · C` over `A` is checked on the basis
  vectors `Pi.single j 1`. Each side is compared through all functionals `ℓ` on `A`
  (`vector_ext_of_functionals`) and the Library lemma `linearFunctional_mulVec_rectangular`.
- `Intertwines.toModuleMap`, `intertwines_toMatrix'`,
  `exists_intertwines_bijective_of_linearEquiv` and `Intertwines.toLinearEquiv`: an
  intertwining matrix gives a module map, and the matrix of a module map intertwines.
  A module isomorphism `OperatorModule ρ ≃ OperatorModule σ` gives a matrix `C` with
  `Intertwines ρ σ C` and `Function.Bijective C.mulVecLin`, and conversely.

## Irreducibility and semisimplicity

- `isIrreducible_of_isSimpleModule`: if `OperatorModule ρ` is a simple module, then
  `ρ.IsIrreducible` (nontriviality of `n → k`, and every stable subspace is `⊥` or `⊤`).
  It uses `eq_bot_of_toSubmodule_eq_bot` and `eq_top_of_toSubmodule_eq_top`.
- `isSemisimpleModule_of_sSup_eq_top`: if the simple stable subspaces of `n → k` span it,
  in exactly the form of the local predicate `IsSemisimpleRep` of
  `SplitRepresentationCharacterStatement`, then `OperatorModule ρ` is a semisimple module.
  Each simple stable subspace `W` gives a simple submodule `W.toSubmodule`. Its
  submodules are `toSubmodule`s of stable subspaces of `W`. The sum of all simple
  submodules therefore contains every such `W` and is `⊤`, and Mathlib's
  `IsSemisimpleModule.of_sSup_simples_eq_top` applies.

## Coordinates on submodules

`exists_linearEquiv_submodule` (needs `[IsAffineHom G.X.hom]`): every submodule `S` of
`OperatorModule ρ` is isomorphic, as a module over the operator algebra, to
`OperatorModule τ` for some `τ : MatrixRepresentation G (Fin r)`. The coordinate subspace
`V` of `S` is stable. The Library lemma `exists_subspace_split_coordinates` gives a matrix
`B : Matrix n (Fin r) k` whose columns lie in `V` and a matrix `P` with `P B = 1` and
`(B P) v = v` for every `v ∈ V`.
`IsStableSubspace.isStableCoordinates` and `restrictCoordinates` then give the
subrepresentation `τ` on `Fin r → k`, and `B` intertwines `τ` with `ρ`
(`intertwines_restrictCoordinates`). The module map of `B` is injective because
`P B = 1`, and its range is `S`. So it is an isomorphism onto `S`.

## Direct sums

For a finite family `τ i : MatrixRepresentation G (ν i)`, the Library's
`directSum τ` acts on `(Σ i, ν i) → k`.

- `blockProjection i` restricts a vector to block `i`. It commutes with coefficient
  operators (`blockProjection_coefficientOperator`), which gives the module maps
  `blockModuleMap τ i`. The proof uses the Library lemma `directSum_affineMatrix_val`
  (module `MatrixRepresentation.SemisimpleDirectSum`): the affine matrices of
  `directSum τ` are the block-diagonal matrices `Matrix.blockDiagonal'` of the
  `(τ i).affineMatrix A x`.
- `directSumModuleEquiv`: `OperatorModule (directSum τ)` is isomorphic to the product
  module `∀ i, OperatorModule (τ i)`.

## Provenance

The construction is internal and has no literature counterpart. It encodes the classical
fact that a representation of an affine group scheme is the same as a comodule, and that
subcomodules and comodule maps can be tested with coefficient functionals. The free algebra
on all coefficient operators is a device that makes Mathlib's simple and semisimple module
API available. It does not change the notions of stable subspace, intertwiner,
irreducibility or semisimplicity used in the Library, as the comparison theorems above show.
