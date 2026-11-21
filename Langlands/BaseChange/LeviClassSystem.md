# Levi class systems in a regular semisimple conjugacy class

Let `K` be a field, `B` a standard block shape of `n`, and `M = B.Levi K` the
standard block Levi `GL_{n_1}(K) × ⋯ × GL_{n_r}(K)`, included in `GL_n(K)` by
the Library's block diagonal embedding `B.leviEmbedding K`.

## Definition

`IsLeviClassSystem B γ m`, for `γ ∈ GL_n(K)` and a finite family
`m : Fin k → M`, says that `m` is a system of representatives, without
repetition, of the `M(K)`-conjugacy classes of those elements of `M(K)` whose
block diagonal embedding is `GL_n(K)`-conjugate to `γ`. Precisely:

1. each `m j` lies in this set: some `x ∈ GL_n(K)` has
   `x⁻¹ γ x = leviEmbedding (m j)`;
2. no two members are `M(K)`-conjugate: `y⁻¹ (m j) y = m j'` for some `y ∈ M(K)`
   forces `j = j'`;
3. every element `m'` of the set is `M(K)`-conjugate to some `m j`.

The empty family is a Levi class system exactly when no element of `M(K)` is
conjugate to `γ` in `GL_n(K)`.

This is the index set of Henniart–Lemaire (2011), II.4.5, printed pp. 87–88
(PDF pp. 95–96). For a maximal torus `T` of `M` over `F` and `γ ∈ T(F)` regular,
they sum over the set `W` of maps `Z_M(F) → A_T(F)` of the form `a ↦ g a g⁻¹`
with `g ∈ G(F)`, evaluated at `γ_η = g_η⁻¹ γ g_η`. Let `X` be the set of
`g ∈ G(F)` with `g⁻¹ γ g ∈ M(F)`. For regular `γ` this is the set of `g` with
`g⁻¹ T g ⊆ M`. Equivalently, `g Z_M g⁻¹ ⊆ T`, because `M` is the centralizer of
`Z_M` and every maximal torus of `M` contains `Z_M`. The map `g ↦ Ad(g)|_{Z_M}`
identifies `X / M(F)` with `W`. Two elements `g⁻¹ γ g` and `g'⁻¹ γ g'` are
`M(F)`-conjugate exactly when `g' ∈ T(F) g M(F)`, and `T(F)` acts trivially on
`X / M(F)`. Hence `W` is in bijection with the `M(F)`-conjugacy classes in
`M(F)` of elements conjugate to `γ`, by `η ↦ γ_η`. Sums of `M(F)`-conjugation
invariant functions over the two index sets agree. This derivation is ours. The
Lean definition does not mention tori or `W`.

## Supporting results

- `charpoly_conj`: conjugation in `GL_r` does not change the characteristic
  polynomial (any commutative ring).
- `isRegularSemisimple_conj`: conjugation preserves the Library's
  `IsRegularSemisimple` (separable characteristic polynomial).
- `charpoly_dvd_of_leviEmbedding`: the characteristic polynomial of each block
  divides that of the block diagonal element.
- `isRegularSemisimple_block`: the blocks of a regular semisimple block diagonal
  element are regular semisimple.
- `exists_isLeviClassSystem`: every regular semisimple `γ ∈ GL_n(K)` has a
  finite Levi class system, over any field.

## Proof of `exists_isLeviClassSystem`

Let `χ` be the characteristic polynomial of `γ`, which is monic and separable.
If `x⁻¹ γ x = leviEmbedding m'`, then `χ` is the product of the block
characteristic polynomials of `m'` (the Library's `charpoly_leviEmbedding`).
So each block polynomial is a monic divisor of `χ`. Mathlib's
`Polynomial.fintypeSubtypeMonicDvd` shows that `χ` has finitely many monic
divisors. The tuple map `m' ↦ (charpoly (m' i))_i` therefore has finite image on
the set above. Choose one preimage of each point of this finite image, indexed
by `Fin k` through an enumeration of the image.

Conjugation in `M(K)` does not change the tuple, so distinct indices give
non-conjugate representatives. Conversely, let two elements of the set have the
same tuple. Each block has a separable characteristic polynomial, since it
divides `χ`. The Library's `exists_matrix_conj_of_charpoly_eq_of_separable`
then gives a conjugating element in each block, and these assemble to an element
of `M(K)`. So every element of the set is conjugate to the chosen representative
of its tuple.
