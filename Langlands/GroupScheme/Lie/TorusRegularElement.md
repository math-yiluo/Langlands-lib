# Regular elements in the Lie algebra of a split torus

Author: Worker 1630.

This derived helper module proves the following. Let `S` be a split torus over
an infinite field with a homomorphism `S ⟶ H` into an affine algebraic group.
Then `Lie(S)` has a Lie element `Y` such that the image of `ad(Y)` and the
centralizer of `Lie(S)` span `Lie(H)`. This is the linear-algebra input for
dominance of the adjoint slice map in the project's route to unirationality
of the scheme of maximal tori (SGA 3, Exposé XIV). In the classical
argument, `Y` is a regular element of the torus Lie algebra: it avoids the
finitely many proper subspaces on which some root vanishes. The proof is
written out here from the Library's weight decomposition of the Lie algebra
under a split torus and Mathlib's lemma that a vector space over an infinite
field is not a finite union of proper subspaces. No external theorem is
asserted.

All declarations live in the namespace `Langlands.GroupScheme.Lie`. The Lie
algebra is the Library's dual-number kernel `lieKernel G A`. Finite Lie
coordinates `c : FiniteCoordinates G d` identify it with `Fin d → A`, and
`adjointDifferentialFamily c Y` is the coordinate matrix of `ad(Y)`.
`targetMap i A` maps Lie elements along a homomorphism `i`. `weightSpace i χ`
is the Library weight space of a character `χ`: the Lie elements of `G` on
which conjugation by `i(t)` is multiplication by `χ(t)`, for points `t` of
the torus over every test algebra.

## Linear algebra

- `exists_range_add_commonKernel`: let `K` be an infinite field and
  `A : L →ₗ[K] End(V)` a linear family of endomorphisms of a vector space `V`.
  Assume `V` is the supremum of subspaces `W χ`, only finitely many of them
  nonzero, and that each `A y` acts on each `W χ` by a scalar. Then there is a
  parameter `y` such that every `v ∈ V` is `A y u + z` with `A y' z = 0` for
  all `y'`.

  Proof. For each `χ`, let `P χ` be the subspace of parameters that
  annihilate `W χ`. The proper subspaces among `P χ` with `W χ ≠ 0` are
  finitely many. Mathlib's `Submodule.exists_forall_notMem_of_forall_ne_top`
  gives `y` outside all of them. If `P χ` is everything, `W χ` lies in the
  common kernel. Otherwise `A y` acts on `W χ` by a nonzero scalar, so `W χ`
  lies in the range of `A y`. Hence `V` is the sum of the range of `A y` and
  the common kernel.

## Weights

Here `R` is a commutative ring, `G` is a group scheme over `Spec R` with
affine structure morphism, `T` is a commutative group scheme over `Spec R`,
and `i : T ⟶ G`.

- `adjointDifferentialFamily_targetMap_of_mem_weightSpace`: if `X` lies in
  the weight space of `χ`, then for every Lie element `Y` of `T`,
  `ad(i Y)` multiplies the coordinates of `X` by the epsilon part of
  `χ(Y)`. Proof: apply the weight-space equation to the dual-number point
  `Y` and the constant lift of `X`. Then compare epsilon coefficients using
  the formula `equiv_adjoint_constant` from `AdjointDominance`.
- `targetMap_mem_weightSpace_zero`: the image of a Lie element of `T` has
  weight zero, since `T` is commutative.
- `adjointDifferentialFamily_targetMap_targetMap`: `ad(i Y') (i Y) = 0` for
  Lie elements `Y`, `Y'` of `T`.

## A regular element

Here `K` is a field, `H` is a group scheme over `Spec K` with affine structure
morphism, locally of finite type, with finite Lie coordinates `cH`, `S` is a
commutative group scheme over `Spec K` with affine structure morphism, and
`i : S ⟶ H`. Coordinates are taken over `K` itself.

- `weightCoordinates cH i χ` (definition): the image of the weight space of
  `χ` in coordinates.
- `torusAdjointFamily cH i` (abbreviation): the `K`-linear family
  `Y ↦ ad(i Y)` of endomorphisms of `K^d`, parametrized by `Lie(S)`.
- `iSup_weightCoordinates` and `finite_weightCoordinates_ne_bot`: if `S` is
  a split torus, the weight coordinates span `K^d` and only finitely many of
  them are nonzero. Both come from the Library's
  `isInternal_weightSpace_of_isSplitTorus`. Finiteness uses independence of
  the weight spaces (`Submodule.finite_ne_bot_of_iSupIndep`).
- `torusAdjointFamily_eigen`: each `ad(i Y)` acts on each weight
  coordinate space by a scalar.
- `exists_regular_targetMap`: assume `K` is infinite and `S` is a split
  torus. Then there is a Lie element `Y` of `S` with two properties. First,
  `ad(i Y') (i Y) = 0` for every Lie element `Y'` of `S`. Second, every
  `v : Fin d → K` is `ad(X) (i Y) + z` for some Lie element `X` of `H` and
  some `z` annihilated by every `ad(i Y')`. Proof: apply
  `exists_range_add_commonKernel` to the torus family. Rewrite
  `ad(i Y) u = ad(X) (i Y)` with `X` the Lie element with coordinates `-u`,
  by the antisymmetry `adjointDifferentialFamily_antisymm` from
  `AdjointDominance`.

The field `K` must be infinite. No smoothness or connectedness hypothesis is
placed on `H`.
