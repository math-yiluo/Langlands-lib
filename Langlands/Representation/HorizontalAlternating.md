# Horizontal equivariant alternating maps

This module is an internal algebraic construction. It defines actual subspaces
of alternating maps, their coefficient transport, and their degree-zero
identification. It prepares the underlying spaces for a later relative
cochain construction; it does not define a differential or cohomology.

The namespace is `Langlands.HorizontalAlternating`. The scalar ring `R` is any
commutative ring and `G` is any group. The domain `M` and coefficient modules
`V`, `W`, and `Z` are additive commutative groups with `R`-module structures.
The ring, group, and each module have independent universes. The inputs are an
arbitrary submodule `H : Submodule R M`, representations
`σ : Representation R G M` and `ρ : Representation R G V`, and a natural degree
`q`, including zero.

## The subspaces

Write `Alt^q_R(M,V)` for Mathlib's alternating multilinear maps
`M [⋀^Fin q]→ₗ[R] V`. The module defines:

* `horizontal H q`: the submodule of maps `f` such that, for every tuple
  `x : Fin q → M` and index `i`, membership `x i ∈ H` implies `f x = 0`.
* `equivariant σ ρ q`: the submodule of maps satisfying
  `f (fun i => σ g (x i)) = ρ g (f x)` for every `g : G` and every tuple `x`.
* `submodule H σ ρ q`: the intersection of these two actual submodules.

The zero, addition, and scalar closure obligations follow pointwise from the
module laws and linearity of the representations. `mem_submodule` exposes
the two defining conditions as an equivalence.

Equivariance quantifies over the entire group. There is no topology or
connectedness restriction. No stability of `H` under `σ` is needed to define
this intersection. The construction does not claim an induced action on the
quotient `M/H`, an identification with quotient-valued alternating maps, or
stability under any differential.

## Coefficient transport

For an actual Mathlib intertwiner
`A : Representation.IntertwiningMap ρ τ`, `mapCoefficients H σ q A`
is the linear map between the two subspaces defined by postcomposition:

`(mapCoefficients H σ q A f).val x = A (f.val x)`.

This is Mathlib's `LinearMap.compAlternatingMap` restricted to the subspaces.
Horizontality follows because a linear map sends zero to zero. Equivariance
follows from the source equivariance and the intertwining identity
`A (ρ g v) = τ g (A v)`. The linearity obligations use Mathlib's pointwise
addition and scalar multiplication identities for postcomposition.

`mapCoefficients_id` and `mapCoefficients_comp` give the identity and composition
laws. `mapCoefficients_injective` proves injectivity when the coefficient map
`A` is injective, by evaluating at each tuple and applying that injectivity.
It makes no surjectivity claim for arbitrary coefficient maps.

For `e : Representation.Equiv ρ τ`, `coefficientEquiv H σ q e` is the resulting
linear equivalence between subspaces. The forward map is postcomposition by
`e`, and the inverse is postcomposition by `e.symm`. The inverse identities
hold pointwise using the underlying coefficient linear equivalence.
`coefficientEquiv_apply` records the evaluation formula.

## Degree zero

`degreeZeroEquiv H σ ρ` is the linear equivalence

`submodule H σ ρ 0 ≃ₗ[R] ρ.invariants`.

Here `ρ.invariants` is Mathlib's submodule of vectors fixed by every element
of `G`. The forward map evaluates the alternating map on the unique empty
tuple, written `0 : Fin 0 → M`. Equivariance gives
`ρ g (f.val 0) = f.val 0`, since every map out of `Fin 0` is equal.

The inverse sends a fixed vector `v` to
`AlternatingMap.constOfIsEmpty R M (Fin 0) v.val`. Horizontality is vacuous
because an index in `Fin 0` cannot exist; equivariance is exactly the
fixed-vector property. The two inverse identities use uniqueness of the
empty tuple and evaluation of a constant map. Addition and scalar
multiplication are preserved by evaluation. `degreeZeroEquiv_apply` gives
the forward evaluation formula.

## Provenance and scope

This is a source-free internal construction from the defining conditions of
linear subspaces and Mathlib's existing alternating maps, representations,
intertwiners, and invariants. The implementation imports
`Mathlib.LinearAlgebra.Alternating.Basic` and
`Mathlib.RepresentationTheory.Invariants`; no new assertion of correspondence
with an original mathematical source is made.

There is no Lie bracket, Lie-module action, coefficient differentiation,
finite-dimensionality assumption, archimedean specialization, or compatibility
between group and Lie actions in this module. In particular the degree-zero
result concerns the underlying space, not zeroth cohomology: no closedness
condition has been imposed. The relative differential, its preservation of the
subspace, its square-zero law, and a cohomological infinity criterion remain
separate constructions.
