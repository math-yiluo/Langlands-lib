# Characters of the upper unipotent group factor through the first superdiagonal

Author: Worker 784. This module is an internal prerequisite of the exact proof task
`62de5903-b616-4b5c-88eb-a066b77c5467`, which proves
`Langlands.Whittaker.SupercuspidalCoinvariantFinitenessStatement`. It contains only
group theory. Representations, topology, additive self-duality and derivatives do not
appear.

Throughout, `F` is an arbitrary field. `upperUnipotent (n + 1) F` is the published subgroup
of `GL_(n+1)(F)` of upper triangular matrices with diagonal entries one, from
[`Group/GL/UpperUnipotent`](../../Group/GL/UpperUnipotent.md). `M` is an arbitrary
commutative group, in an independent universe.

## Provenance

The statements are a Lean form of Bernstein–Zelevinsky (1976), *Representations of the
group GL(n,F) where F is a non-Archimedean local field*, §5.5 and §5.6 (printed page 45).
The source is registered as `bernstein-zelevinsky-1976-representations-gln`, SHA-256
`72dc22eb9991112936a88327f00d0f02a16a2bf8747518ca0ecfeeadd188e50c`. Printed pages equal
PDF pages.

- In §5.5 the map `U → F^(n-1)`, `(u_ij) ↦ (u_12, …, u_(n-1,n))`, identifies the
  commutator quotient of `U` with `F^(n-1)`. Together with §5.3, which says that every
  additive character of `F` has the form `x ↦ ψ_0(a x)`, this gives
  `θ(u) = ψ_0(∑ a_i u_(i,i+1))`.
- In §5.6 every nondegenerate character is conjugate to `θ(1, …, 1)` under the diagonal
  matrices.

This module proves the part of §5.5 that needs no additive duality: every character into
a commutative group is the product of its restrictions to the adjacent elementary
matrices (`eq_prod_adjacentUnit`). It does not prove that the commutator quotient is
exactly `F^(n-1)`. For the conjugation part of §5.6 it gives the explicit diagonal
conjugation that rescales the superdiagonal (`diagonalConj_tailProduct_adjacent`). The
route is internal: induction on the rank, using the published decomposition of the
mirabolic group into its radical and the successor image.

## Elementary matrices

- `transvection_apply` writes the entries of Mathlib's `Matrix.transvection i j c`, which
  is `1 + Matrix.single i j c`, as `δ_ab + (if i = a ∧ j = b then c else 0)`.
- `upperTransvection i j hij c`, for `i < j`, is the published
  `GeneralLinear.transvectionUnit i j _ c`, viewed as an element of the actual
  upper-unipotent subgroup. `upperTransvection_zero` says that parameter zero gives `1`.
- `adjacentUnit i x : upperUnipotent (n + 1) F`, for `i : Fin n`, is `1 + x E_(i,i+1)`,
  with `i` read as `i.castSucc` and `i+1` as `i.succ`. `adjacentUnit_zero` gives
  `adjacentUnit i 0 = 1`. `adjacentUnit_add` gives
  `adjacentUnit i (x + y) = adjacentUnit i x * adjacentUnit i y`.
- `adjacentCharacter η i : Multiplicative F →* M` is the homomorphism
  `x ↦ η (adjacentUnit i x)`. `adjacentCharacter_apply` is its defining equation.

## Successor and radical columns

- `successor_mem_upperUnipotent` says that the published successor embedding
  `GeneralLinear.Mirabolic.successor : P_(n+1) → P_(n+2)`, `g ↦ diag(g, 1)`, maps upper
  unipotent matrices to upper unipotent matrices.
- `successorUnipotent n : U_(n+1) →* U_(n+2)` is that embedding restricted and
  corestricted, built with `MonoidHom.codRestrict`. `successorUnipotent_val` identifies
  its underlying matrix with the published `levi` matrix. `successorUnipotent_first`,
  `_last` and `_bottom` give its entries. `successorUnipotent_adjacentUnit` says that it
  sends `adjacentUnit i x` to `adjacentUnit i.castSucc x`.
- `radicalUnipotent n c : U_(n+2)` is the published radical element
  `radicalElement c = [[I, c], [0, 1]]`, mapped by the published `radicalToUpperUnipotent`.
  `radicalUnipotent_add` and `radicalUnipotent_zero` say that `c ↦ radicalUnipotent n c`
  is additive in `c`. `radicalUnipotent_single_last` says that the column supported in the
  last coordinate is the adjacent elementary matrix `adjacentUnit (Fin.last n) x`.
- `character_radicalUnipotent_single_castSucc`: a column supported in a coordinate
  `k.castSucc < n` is a commutator in `U_(n+2)`. It equals `r⁻¹ (s r s⁻¹)`, where `r` is
  the column `e_n` and `s` is the successor of the transvection `1 + x E_(k,n)`. This
  identity comes from the published `levi_conjugate_radicalElement`. Every homomorphism
  into a commutative group therefore kills such a column.
- `character_radicalUnipotent`: hence `η (radicalUnipotent n c)` equals
  `η (adjacentUnit (Fin.last n) (c (Fin.last n)))`. Only the last coordinate of the
  column matters.

## Decomposition and factorization

- `exists_radical_mul_successor n u`: every `u : U_(n+2)` equals
  `radicalUnipotent n c * successorUnipotent n h`, where `c` is the last column of `u`
  above the diagonal and `h : U_(n+1)` has the upper-left entries of `u`. The proof
  applies the published `exists_successor_eq` from
  [`SupercuspidalDerivativeVanishing`](../Classification/SupercuspidalDerivativeVanishing.md)
  to `radicalElement (-c) * u`.
- `eq_prod_adjacentUnit n η u` is the main theorem. For every homomorphism
  `η : U_(n+1) →* M` into a commutative group and every `u`,

  ```text
  η u = ∏ i : Fin n, η (adjacentUnit i (u_(i,i+1)))
  ```

  The proof is by induction on `n`. Rank one is the trivial group. In the inductive step,
  `exists_radical_mul_successor` splits `u`. The radical factor contributes the last
  adjacent term, by `character_radicalUnipotent`. The induction hypothesis, applied to
  `η ∘ successorUnipotent n`, gives the remaining terms.

## Block unipotent matrices

`IsBlockUnipotent m g` is the published predicate of
[`SupercuspidalDerivativeVanishing`](../Classification/SupercuspidalDerivativeVanishing.md):
the first `m` columns and the rows from `m` on are those of the identity matrix, so that
`g = [[I_m, Y], [0, I]]`.

- `isBlockUnipotent_adjacent_eq_zero`: a matrix with `IsBlockUnipotent (k + 1) g` has
  `g_(i,i+1) = 0` for every `i ≠ k`.
- `character_eq_one_of_isBlockUnipotent`: if `η (adjacentUnit k x) = 1` for all `x`, then
  `η u = 1` for every `u` with `IsBlockUnipotent (k + 1) u`. This is the degeneracy step
  of BZ76 §5.15(a), proof of (2) ⇒ (3), printed page 49: a degenerate character is
  trivial on a nontrivial standard block radical.

## Diagonal conjugation

- `diagonalUnit d`, for `d : Fin m → Fˣ`, is the invertible diagonal matrix with
  explicit inverse `diag(d⁻¹)`. `diagonalUnit_conj_apply` gives the entries
  `(t g t⁻¹)_(ij) = d_i g_(ij) d_j⁻¹`. `diagonalUnit_conj_mem` says that conjugation
  preserves `U_m`.
- `diagonalConj d : U_m →* U_m` is `u ↦ t u t⁻¹` with `t = diagonalUnit d`, the
  restriction of Mathlib's `MulAut.conj`. `diagonalConj_val` is its defining equation.
- `tailProduct a j = ∏_(k : Fin n, j ≤ k) a_k`, for `a : Fin n → Fˣ` and
  `j : Fin (n + 1)`. `tailProduct_castSucc` gives
  `tailProduct a i.castSucc = a i * tailProduct a i.succ`.
- `diagonalConj_tailProduct_adjacent`: conjugation by `diag(tailProduct a)` multiplies
  each first-superdiagonal entry `u_(i,i+1)` by `a_i`.

Together with additive self-duality, this realizes the §5.6 conjugacy. A nondegenerate
character `u ↦ ∏ ψ(a_i u_(i,i+1))` is the standard character `ψ(∑ ·)` composed with
`diagonalConj (tailProduct a)`.
