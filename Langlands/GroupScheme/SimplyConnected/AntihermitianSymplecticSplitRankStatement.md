# The split rank of the symplectic group of an antihermitian form is its Witt index: statement

Author: Worker 31, for Task 5986 (`8494af77-9d10-4c2f-b1cd-60dc371fb195`). The module
contains one `Prop`-valued definition and no proof.

## Statement

`Langlands.GroupScheme.AntihermitianSymplecticSplitRankStatement.{u}` quantifies over

- a field `K : Type u`;
- a division ring `D : Type u` which is a central, finite-dimensional `K`-algebra;
- natural numbers `degree` and `m`, with `NeZero m`;
- an involution of the first kind `σ : Quaternionic.FirstKindInvolution K D`;
- a Gram matrix `H : Matrix (Fin m) (Fin m) D`.

It assumes

- `Module.finrank K D = degree ^ 2`;
- `Module.finrank K σ.symmetricSubspace = degree * (degree + 1) / 2`;
- `σ.IsAntihermitian H`: `ᵗH^σ = -H` and every diagonal entry `H i i` lies in `{a - σ a}`;
- `IsUnit H`.

The statement then asserts the equality in `ℕ∞`

`splitRank (σ.symplecticGroup H) = σ.wittIndex H`.

Here `splitRank` (module `Rational/SplitTorus`) is the supremum of the ranks of split tori
admitting a closed-subgroup homomorphism into the group, `σ.symplecticGroup H` (module
`Quaternionic/GroupSchemes`) is the kernel of the reduced norm on the unitary group scheme
of `H`, and `σ.wittIndex H : ℕ` (module `Quaternionic/Forms`) is the largest `D`-dimension of a
totally isotropic left `D`-subspace of `D^m` for the form
`h(x, y) = ∑ i j, x i * H i j * σ (y j)`. The natural Witt index is cast to `ℕ∞`.

The hypotheses are exactly the algebra, involution and form conditions produced by
`SymplecticInnerFormAntihermitianStatement` and appearing in the published
`TypeCDivisionFormStatement`; the degree conditions are kept so that the statement concerns
the type-`C` groups of Tits's table. The size `m` and the Witt index are arbitrary, including
Witt index zero (anisotropic forms).

## Intended proof (not part of the statement)

For a totally isotropic subspace with a `D`-basis `w_1, …, w_r`, extend to a hyperbolic
decomposition `D^m = (W ⊕ W') ⊥ U` with `W, W'` totally isotropic and dual. The scalar
matrices `t_i` on `w_i`, `t_i^{-1}` on the dual vector, and `1` on `U` give a closed embedding
of `G_m^r` into `σ.symplecticGroup H`, so `wittIndex ≤ splitRank`. Conversely a split torus
in the unitary group diagonalizes `D^m` into weight spaces; weight spaces for weights `χ` and
`ψ` with `χ + ψ ≠ 0` are orthogonal, so each nonzero weight space is totally isotropic and
the rank of the torus is at most the Witt index. For infinite `K`, the Library already proves
the special cases `splitRank (σ.symplecticGroup H) ≤ 1` when `σ.wittIndex H ≤ 1` (module
`Quaternionic/TorusWittBound`) and `splitRank = 1` when `σ.wittIndex H = 1` and `m ∈ {2, 3}`
(module `Quaternionic/SymplecticSplitRank`), by these arguments.

## Role

This is one of four prerequisites in the planned proof of `TypeCDivisionFormStatement`
(Task 5986). It supplies the clause `(σ.wittIndex H : ℕ∞) = splitRank G` of the target after
transport along `G ≅ σ.symplecticGroup H` by the published `splitRank_eq_of_iso`.

## Source and provenance

Provenance: derived.

1. J. Tits, *Classification of algebraic semisimple groups*, in *Algebraic Groups and
   Discontinuous Subgroups*, Proc. Sympos. Pure Math. 9, 1966, source
   `tits-1966-classification-algebraic-semisimple`, SHA-256
   `962203f9e47e9c3c43fc1049a38e28c751aa42beb7ee5250a095a132e215a5d4`:
   - Table II, Explanations, printed p.54 (PDF p.59): in each index symbol `r` is the relative
     rank of the group, equal to the number of distinguished orbits;
   - Table II, type `C_n`, printed p.56 (PDF p.61): the group of index `C^{(d)}_{n,r}` is
     `SU_{2n/d}(D, h)` with `D` of degree `d`, `h` a nondegenerate antihermitian form "of
     index `r`" relative to an involution of the first kind with `dim D^σ = d(d + 1)/2`.
   So the relative rank of `SU_{2n/d}(D, h)` is the Witt index of `h`.
2. M.-A. Knus, A. Merkurjev, M. Rost and J.-P. Tignol, *The Book of Involutions*, AMS
   Colloquium Publications 44, 1998, source `knus-merkurjev-rost-tignol-1998-book-of-involutions`,
   SHA-256 `e21641aeb1425b63bec70032352f0cb33275f7bd1ddf682c3bea62b798654fe0`, §2,
   Proposition (2.6), printed pp.16–17 (PDF pp.39–40), and §4, Theorem (4.2), printed p.43
   (PDF p.66). These identify the hypotheses: when `char K ≠ 2` the dimension condition
   makes `σ` orthogonal and the adjoint involution of the antihermitian `h` symplectic; when
   `char K = 2` the dimension condition holds for every involution of the first kind and the
   trace-valued (alternating) condition makes the adjoint involution symplectic. In both cases
   `σ.symplecticGroup H` is a simply connected group of type `C`.

The Lean statement is derived from these sources as follows. Tits's relative rank is the
published `splitRank`, his "index of `h`" is the published `wittIndex`, and his
`SU_{2n/d}(D, h)` is the published group scheme `σ.symplecticGroup H`. Tits works with groups
of rational points and lists the forms; the statement is the rank equality alone, for every
size `m` and every field, including characteristic two.
