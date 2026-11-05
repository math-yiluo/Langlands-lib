# Stable subspaces are detected by rational points and by tangent matrices

Author: Worker 1498.

This module is an internal helper for the proof of
`Langlands.GroupScheme.ReductiveCharZeroSemisimplicityStatement`. Fix a finite
matrix representation `ρ : MatrixRepresentation G n` of a group scheme `G` over a
field `k`, and a subspace `W` of `n → k`. The module compares three kinds of
stability of `W`:

1. `ρ.IsStableSubspace W`, stability on every affine test (Library definition
   in `MatrixRepresentation.StableSubrepresentation`). For every `k`-algebra
   `A`, every `A`-point `x` of `G`, every `v ∈ W` and every `k`-linear
   `ℓ : A → k`, the vector `i ↦ ℓ((ρ_A(x) v)_i)` lies in `W`;
2. stability under the rational-point matrices `ρ.rationalMatrix g`;
3. stability under every tangent matrix `ρ.tangentMatrix k X`, for
   `X ∈ lieKernel G k`.

## Declarations

- `mulVec_mem_of_columns`: if every column of `B` lies in `W`, then so does
  `B *ᵥ w`.
- `IsStableSubspace.rationalMatrix_mulVec_mem` ([IsAffineHom]): 1 implies 2.
- `IsStableSubspace.tangentMatrix_mulVec_mem`: 1 implies 3.
- `isStableSubspace_of_rationalMatrix` and `isStableSubspace_iff_rationalMatrix`:
  if `k` is algebraically closed and `G.X.left` is reduced and locally of finite
  type over `k`, then 2 implies 1. With `IsAffineHom` they are equivalent.
- `exists_basis_coordinateSubspace`: every subspace `W` of `n → k` is cut out by
  the vanishing of some coordinates of some basis `b` indexed by `n`. That is,
  `v ∈ W ↔ ∀ i ∉ S, b.repr v i = 0` for a set `S ⊆ n`.
- `mem_comap_blockParabolic_affine`: an affine point lies in the inverse image
  under `σ` of the block parabolic of a weight `e : n → ℤ` iff its matrix
  vanishes at every entry `(i, j)` with `e i < e j`.
- `intertwines_conjugate_basisCoordinatePoint`: the basis-coordinate matrix of
  `b` intertwines `ρ` with its conjugate by `basisCoordinatePoint b`.
- `comap_blockParabolic_eq_top` ([CharZero], affine, locally of finite type,
  smooth, connected): if every tangent matrix of `ρ` vanishes at the entries
  `(i, j)` with `e i < e j`, then the inverse image of the block parabolic of `e`
  is the whole group.
- `isStableSubspace_of_tangentMatrix` and `isStableSubspace_iff_tangentMatrix`
  (same hypotheses): 3 implies 1, so 1 and 3 are equivalent.

Under the hypotheses of the final theorem (algebraically closed, characteristic
zero, smooth, affine, connected), the three notions coincide.
`PairLieAlgebra` combines the two equivalences to pass between rational
subrepresentations and tangent-stable subspaces.

## Proofs

**1 ⇒ 2.** Choose split coordinates `B`, `C` for `W`
(`exists_subspace_split_coordinates`). Stability on every test gives
`IsStableSubspace.isStableCoordinates`, an identity of matrices over the global
sections of the test. On the base point it becomes
`ρ(g) B = B (C ρ(g) B)` over `k`, after transport along
`Γ(Spec k) ≅ k`. Writing `v = B (C v)` gives `ρ(g) v = B(⋯) ∈ W`.

**1 ⇒ 3.** Apply the definition to the test `k[ε]`, the point `X`, and the
functional `ℓ = snd`, which takes the `ε`-coefficient. The matrix of `X` is
`1 + εM` with `M = ρ.tangentMatrix k X`, and the `ε`-coefficient of
`(1 + εM) v` is `M v`.

**2 ⇒ 1.** With split coordinates `B`, `C` for `W`, stability under rational
matrices gives `ρ(g) B = B (C ρ(g) B)` for every rational point `g`. The Library
criterion `isStableCoordinates_of_rationalMatrix` extends this to all tests; it
uses that `G` is reduced, locally of finite type, and has dense rational points.
The restriction `intertwines_restrictCoordinates` then shows that the range of `B`,
which is `W`, is stable.

**3 ⇒ 1.** Choose `b` and `S` with `W = {v | ∀ i ∉ S, b.repr v i = 0}`. Let `U`
be the basis-coordinate matrix, so `U v = b.repr v`, and let `ρ'` be the conjugate
of `ρ` by `U`. Then `W` is the inverse image under `U` of the coordinate subspace
`C = {c | ∀ i ∉ S, c i = 0}`. Tangent stability of `W` means that every tangent
matrix of `ρ'` maps `C` into `C`, that is, its entry `(i, l)` vanishes when `i ∉ S`
and `l ∈ S`. For the weight `e = 1_S` these are exactly the entries with
`e i < e l`.

`comap_blockParabolic_eq_top` then shows that `ρ'` maps all of `G` into the block
parabolic of `e`. The inverse image `F` of the block parabolic is represented by a
closed subgroup `H → G`
(`isRepresentedBy_blockParabolic.comap_subgroupIntersectionFst`), and `H` is
affine and locally of finite type over `k`. In characteristic zero it is smooth
(Cartier's theorem, `affineCartierSmooth`). Its tangent submodule is everything,
because each tangent point `1 + εM` of `ρ'` satisfies the parabolic vanishing
condition. Rigidity for smooth closed subgroups of a smooth connected group,
`RelativeRoot.eq_top_of_smooth_closed_of_tangentSubmodule_eq_top`, gives `F = ⊤`.

So on every test every matrix of `ρ'` vanishes at the entries `(i, l)` with
`i ∉ S`, `l ∈ S`, and hence maps `C` into itself on every test. Therefore
`ρ'.IsStableSubspace C`. Transporting back along `U` (`IsStableSubspace.comap`
with the intertwiner) gives `ρ.IsStableSubspace W`.
