# The distinguished vertices of a symplectic group of an antihermitian form: statement

Author: Worker 31, for Task 5986 (`8494af77-9d10-4c2f-b1cd-60dc371fb195`). The module
contains one `Prop`-valued definition and no proof.

## Statement

`Langlands.GroupScheme.TypeCDistinguishedVerticesStatement.{u}` quantifies over

- a field `K : Type u`;
- a group scheme `G` over `Spec K` with `IsAffineHom G.X.hom` and
  `LocallyOfFiniteType G.X.hom`;
- actual index data `d : TitsIndexData G` (module `Reductive/TitsIndex`);
- a natural number `n` and a numbering `e : d.Vertex ≃ Fin n` of the simple vertices.

It assumes, exactly as the published `TypeCDivisionFormStatement` does,

- `2 ≤ n`, `IsSimplyConnected G` and `IsAbsolutelyAlmostSimple G`;
- `d.cartan a b = CartanMatrix.C n (e a) (e b)` for all simple vertices `a b`.

It further quantifies over a presentation of `G` of the shape produced by
`SymplecticInnerFormAntihermitianStatement`:

- natural numbers `degree` and `m`, with `NeZero m`, `0 < degree` and `m * degree = 2 * n`;
- a division ring `D : Type u` which is a central, finite-dimensional `K`-algebra with
  `Module.finrank K D = degree ^ 2`;
- an involution of the first kind `σ` of `D` with
  `Module.finrank K σ.symmetricSubspace = degree * (degree + 1) / 2`;
- a Gram matrix `H : Matrix (Fin m) (Fin m) D` with `σ.IsAntihermitian H` and `IsUnit H`;
- the hypothesis `Nonempty (G ≅ σ.symplecticGroup H)`.

The statement then asserts that for every simple vertex `a`,

`a ∈ d.distinguishedVertices ↔ ∃ j : ℕ, 1 ≤ j ∧ j ≤ σ.wittIndex H ∧ (e a).val + 1 = j * degree`.

Here `d.distinguishedVertices` is the complement of the set of simple vertices whose actual
root restricts to zero on the maximal split torus of `d`, and `(e a).val + 1` is the one-based
number of `a` in the numbering `e`. So the distinguished vertices are those numbered
`degree, 2 * degree, …, r * degree`, where `r = σ.wittIndex H`. The bound uses the natural
Witt index, not the split rank; with `AntihermitianSymplecticSplitRankStatement` the two
agree.

## Intended proof (not part of the statement)

Since the Cartan matrix of type `C_n`, `n ≥ 2`, is not symmetric under any nontrivial
permutation, `e` is the standard (Bourbaki) numbering, with the long simple root last. Pass to
`G' = σ.symplecticGroup H` along the isomorphism, and write `δ = degree` and
`r = σ.wittIndex H`. Choose a Witt decomposition of the form `h` defined by `H` on the right
`D`-module `D^m`: `D`-linearly independent isotropic vectors `w_1, …, w_r` spanning a maximal
totally isotropic submodule, vectors `w'_1, …, w'_r` with `h(w'_i, w'_j) = 0` and `h(w_i, w'_j)`
equal to `1` if `i = j` and `0` otherwise, and an anisotropic orthogonal complement `W_0` of
`D`-rank `m - 2r`. The rank-`r` torus `S` acting by a character `t_i` on `w_i D`, by `t_i^{-1}`
on `w'_i D` and trivially on `W_0` (as in `AntihermitianSymplecticSplitRankStatement`) is a
maximal split torus of `G'`.

To read off the roots, pass to a splitting field `L ⊇ K`, so that `D ⊗_K L ≅ M_δ(L)`. The scalar
extension `D^m ⊗_K L` is a right `M_δ(L)`-module of `L`-dimension `m δ^2 = 2 n δ`; it is not the
natural `2n`-dimensional representation. By Morita equivalence, `D^m ⊗_K L ≅ V ⊗_L L^δ` (row
vectors) for the `L`-vector space `V = (D^m ⊗_K L) ⊗_{M_δ(L)} L^δ` (column vectors), of
dimension `m δ = 2n`, and `h ⊗ L` corresponds to a nondegenerate alternating form on `V`; this
identifies `G'_L` with `Sp(V) ≅ Sp_{2n}` (compare KMRT §4, Theorem (4.2)). Each `D`-line
`w_i D` corresponds to a `δ`-dimensional subspace of `V` on which `S` acts by `t_i`, each `w'_i D`
to one on which it acts by `t_i^{-1}`, and `W_0` to a `2(n - r δ)`-dimensional subspace of
weight zero. Hence `V` has a symplectic basis `v_1, …, v_n, v_{-n}, …, v_{-1}` (with `v_k` paired
with `v_{-k}`) such that `S` acts on `v_k` by `t_j` when `(j - 1) δ < k ≤ j δ` with `j ≤ r`, and
trivially when `k > r δ`. Let `ε_k` be the characters of the diagonal maximal torus in this
basis, so that the roots are `±ε_k ± ε_l` and `±2ε_k`, with simple roots
`ε_1 - ε_2, …, ε_{n-1} - ε_n, 2ε_n`; the restriction of `ε_k` to `S` is `t_j` for
`(j - 1) δ < k ≤ j δ ≤ r δ` and zero for `k > r δ`. Therefore:

- a short simple root `ε_k - ε_{k+1}`, with `k < n`, has nonzero restriction to `S` exactly when
  `k = j δ` for some `j` with `1 ≤ j ≤ r` and `j δ < n` (the restriction is `t_j - t_{j+1}` if
  `j < r` and `t_r` if `j = r`);
- the long simple root `2ε_n`, the vertex numbered `n`, has nonzero restriction exactly when
  `r δ = n` (the restriction is then `2 t_r`).

Since `j δ ≤ r δ ≤ n` for every `j ≤ r`, each number `j δ` with `1 ≤ j ≤ r` falls in exactly one
of these two cases, so the vertices with nonzero restriction are exactly those numbered
`δ, 2δ, …, r δ`. Comparison with the actual index data `d` needs that the set of distinguished
vertices does not depend on the choice of maximal split torus and adapted base, and transport
of this set along the isomorphism `G ≅ G'`.

## Role

This is one of four prerequisites in the planned proof of `TypeCDivisionFormStatement`
(Task 5986). It supplies the distinguished-vertex clause of the target once the Witt index is
identified with the split rank.

## Source and provenance

Provenance: derived.

1. J. Tits, *Classification of algebraic semisimple groups*, in *Algebraic Groups and
   Discontinuous Subgroups*, Proc. Sympos. Pure Math. 9, 1966, source
   `tits-1966-classification-algebraic-semisimple`, SHA-256
   `962203f9e47e9c3c43fc1049a38e28c751aa42beb7ee5250a095a132e215a5d4`:
   - Table II, Explanations, printed pp.54–55 (PDF pp.59–60): `n` and `r` are the absolute
     and relative rank, distinguished orbits are listed in the numbering of vertices of
     Table I, and the classical-type parameter in parentheses is the degree of a division
     algebra;
   - Table II, type `C_n`, printed p.56 (PDF p.61): for the index `C^{(d)}_{n,r}`,
     "Distinguished vertices: `d, 2d, …, rd`", the group being `SU_{2n/d}(D, h)` with `D` of
     degree `d` and `h` a nondegenerate antihermitian form of index `r` relative to an
     involution of the first kind with `dim D^σ = d(d + 1)/2`.
2. M.-A. Knus, A. Merkurjev, M. Rost and J.-P. Tignol, *The Book of Involutions*, AMS
   Colloquium Publications 44, 1998, source `knus-merkurjev-rost-tignol-1998-book-of-involutions`,
   SHA-256 `e21641aeb1425b63bec70032352f0cb33275f7bd1ddf682c3bea62b798654fe0`, §2,
   Proposition (2.6), printed pp.16–17 (PDF pp.39–40), and §4, Theorem (4.2), printed p.43
   (PDF p.66), for the meaning of the hypotheses in every characteristic, as explained in
   `SymplecticInnerFormAntihermitianStatement.md`.

The Lean statement is derived from these sources as follows. The vertices are the actual
simple vertices of `d`, numbered by `e` so that the actual Cartan matrix is Mathlib's
`CartanMatrix.C n`, whose last vertex is the long root as in Tits's Table I. Tits's `d` is
`degree`, his `r` is `σ.wittIndex H`, and his `SU_{2n/d}(D, h)` is the published
`σ.symplecticGroup H`, to which `G` is assumed isomorphic. Tits lists the distinguished
vertices of the index of the isogeny class; the statement asserts the same list for the
distinguished vertices of the actual data `d` of the given group.
