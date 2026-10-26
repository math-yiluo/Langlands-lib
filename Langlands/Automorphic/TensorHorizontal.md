# Tensor coefficients on actual automorphic horizontal spaces

This internal construction starts with an actual
`S : OperatorRealization F n`, for a number field `F : Type u`, and a specified
complex representation `τ` of `standardInfiniteCompact F n` on a complex module
`V : Type v`. The carrier `S.Space` is the existing realized subspace of actual
stable automorphic functions. The coefficient module may have arbitrary
dimension, and its universe is independent of the field universe. All natural
ranks `n` and degrees `q`, including zero, are retained.

The declarations are in `Langlands.Automorphic.OperatorRealization`. Write
`K = standardInfiniteCompact F n`, `Gf = FiniteAdelicGL F n`,
`R(k) = S.compactRepresentation k`, and
`P(d) = S.finiteRepresentation d`. These are the existing positive right
translation operators restricted to the actual realization. The group `K` is
the full standard infinite compact subgroup, including every component of its
real orthogonal factors.

## Tensor actions

`tensorCompactRepresentation τ` is Mathlib's tensor product representation
`S.compactRepresentation.tprod τ` on `S.Space ⊗[ℂ] V`. Its action on pure
tensors is

`k · (f ⊗ v) = R(k) f ⊗ τ(k) v`.

`tensorFiniteRepresentation V` tensors `S.finiteRepresentation` with the
trivial representation of `Gf` on `V`. Thus

`d · (f ⊗ v) = P(d) f ⊗ v`.

The two `_tmul` lemmas record these formulas. No finite adelic coefficient
action is part of the input.

`tensorFiniteRepresentation_compact` proves that these two actions commute
on every tensor. Tensor induction reduces the pure tensor case to the existing
commutation of `P(d)` and `R(k)` on `S.Space`; linearity handles addition.
`tensorFiniteCompactIntertwiner τ d` bundles each finite translation as an
intertwiner of the diagonal compact representation with itself.

## Horizontal spaces and their finite action

`tensorHorizontalSubmodule τ q` is the actual submodule
`ArchimedeanGL.horizontalEquivariantSubmodule F n
  (S.tensorCompactRepresentation τ) q`.
Its elements are complex multilinear alternating maps from
`Fin q → ArchimedeanGL.ReducedComplexLieAlgebra F n` to `S.Space ⊗[ℂ] V`.
For such a map `c`, membership imposes exactly the two existing conditions:

1. `c x = 0` whenever any argument `x i` is the image of a vector in
   `ArchimedeanGL.CompactComplexLieAlgebra F n` under
   `compactToReducedComplex F n`.
2. For every `k : K`,
   `c (fun i => reducedComplexLieConjugation F n k.val (x i))
     = S.tensorCompactRepresentation τ k (c x)`.

The reduced algebra is the existing complexification of the coordinatewise
real-trace kernel. At complex places it retains the imaginary scalar
directions before complexification. Both conditions use the actual matrix
algebras, inclusions and adjoint actions.

`tensorHorizontalFiniteRepresentation τ q` postcomposes these maps with
`tensorFiniteCompactIntertwiner τ d`. Its application formula is

`(d · c).val x = S.tensorFiniteRepresentation V d (c.val x)`.

Postcomposition preserves horizontality and compact equivariance by the
published coefficient-map construction. The one and multiplication laws are
proved by evaluation on each tuple and the corresponding laws of the tensor
finite representation.

`tensorInvariantsFiniteRepresentation τ` restricts finite translation to the
full-compact fixed vectors of `S.tensorCompactRepresentation τ`. Commutation
proves that a finite translate is still fixed by every `k : K`; the
representation laws follow after passing to the underlying tensor.

`tensorHorizontalDegreeZeroEquiv τ` is an equivalence of finite adelic
representations from degree zero to those full-compact fixed vectors.
Its underlying linear equivalence is the published horizontal degree-zero
equivalence, evaluation at the unique empty tuple. The application lemma
writes that tuple as `0`. Evaluation commutes with postcomposition, proving
finite equivariance. This is an equivalence of underlying spaces with their
finite action.

## Maps and equivalences

For an actual full-operator intertwiner `L : S.Intertwiner T` and a compact
coefficient intertwiner `A : τ.IntertwiningMap υ`,
`tensorCompactMap L A` is the tensor product of `L.compactRestriction` and `A`.
Its underlying linear map is `TensorProduct.map L.toLinearMap A.toLinearMap`,
and its pure tensor formula is `f ⊗ v ↦ L f ⊗ A v`.
`tensorCompactMap_finite` proves finite equivariance by tensor induction and
the finite equivariance of `L`.

`tensorHorizontalMap q L A` postcomposes with this compact intertwiner and
bundles the result as an intertwiner of the horizontal finite adelic
representations. Its application lemma evaluates it as
`(tensorCompactMap L A) (c.val x)`. Coefficient targets may lie in a further
independent universe `w`.

For a full-operator equivalence `e : S.Equivalence T` and a compact coefficient
equivalence `a : τ.Equiv υ`, `tensorCompactEquiv e a` uses the genuine tensor
linear equivalence `TensorProduct.congr e.toLinearEquiv a.toLinearEquiv`.
The tensor compact intertwiner proves its equivariance.
`tensorHorizontalEquiv q e a` then uses the published horizontal coefficient
equivalence and the finite equivariance of `tensorHorizontalMap` to give an
equivalence of horizontal finite adelic representations. The final application
lemma identifies it pointwise with that same tensor linear equivalence.

## Provenance and remaining obligations

This module derives its constructions internally from the actual realization
and compact/finite commutation in `OperatorCompactCompatibility`, the spaces
and coefficient maps in `ArchimedeanHorizontal`, and Mathlib's
`Representation.tprod`, `Representation.IntertwiningMap.tensor`,
`TensorProduct.congr` and full-group representation invariants. The proofs
restrict actual linear maps or verify identities by tensor induction and
pointwise evaluation. No new original-literature correspondence is asserted.

Here `τ` is an explicit complex-linear representation of the abstract group
`K`; it is not asserted to arise from a representation
of an algebraic group scheme. Scheme coefficient attachment, its genuine
differential and compatibility with compact differentiation remain separate
obligations. This module constructs no topology, smoothness or differentiability
on the tensor or horizontal spaces. It supplies no tensor Lie action,
relative differential, cycles, boundaries, quotient cohomology or
cohomological infinity criterion. It asserts no nonzero realization,
irreducibility or automorphic occurrence.
