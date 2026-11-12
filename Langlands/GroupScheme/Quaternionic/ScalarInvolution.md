# The scalar involution

Authors: Worker 5196.

Module `Langlands.GroupScheme.Quaternionic.ScalarInvolution`, namespace
`Langlands.GroupScheme.Quaternionic.FirstKindInvolution`. This module defines the identity
involution of a commutative ring regarded as an algebra over itself. It also records how the
published constructions of `Langlands.GroupScheme.Quaternionic.Forms` specialise for this
involution. With it, the published types `(scalar K).QuadraticForms n` and
`(scalar K).isometryGroup q` (module `Langlands.GroupScheme.Quaternionic.GroupSchemes`) are
the ordinary quadratic forms on `K^n` and their orthogonal group schemes, with no new
construction. Universes are arbitrary.

## Definition

- `scalar K : FirstKindInvolution K K`, for a commutative ring `K`, is the published
  structure `FirstKindInvolution` with underlying `K`-linear map `LinearMap.id`. It fixes `1`
  trivially. It reverses products because `K` is commutative (`x * y = y * x`), and it is
  involutive trivially. Its evaluation law is `scalar K x = x` (`scalar_apply`, a simp lemma
  proved by `rfl`). `scalar_toLinearMap` records `(scalar K).toLinearMap = LinearMap.id`.

## Structural lemmas

For a commutative ring `K`:

- `symmetricSubspace_scalar`: `(scalar K).symmetricSubspace = ⊤`. Every element is
  symmetric.
- `alternatingSubspace_scalar`: `(scalar K).alternatingSubspace = ⊥`, because
  `a - scalar K a = a - a = 0`.
- `scalar_matrix_apply`: for a finite index type `n` with decidable equality,
  `(scalar K).matrix n x = x.transpose`. The `σ`-conjugate transpose of the published
  `FirstKindInvolution.matrix` is the plain transpose. The proof is `rfl`.

For a field `K` (the published `Forms` module works over fields):

- `scalar_sesqForm`: `(scalar K).sesqForm H x y = ∑ i, ∑ j, x i * H i j * y j`. This is the
  ordinary bilinear form of the Gram matrix `H` on row vectors.
- `mem_quadraticKernel_scalar`: `x ∈ (scalar K).quadraticKernel n` if and only if
  `x = a - ᵗa` for some matrix `a`. The quotient `(scalar K).QuadraticForms n` is therefore
  `M_n(K) ⧸ {a - ᵗa}`.
- `scalar_polar_mk`: the published polar Gram matrix of the class of `Q` is `Q + ᵗQ`.
- `isNondegenerateQuadratic_scalar_mk_iff`: the class of `Q` is nondegenerate in the
  published sense (`IsNondegenerateQuadratic`, an invertible polar matrix) if and only if
  `Q + ᵗQ` is invertible.
- `scalar_quadraticValue_mk_eq_zero_iff`: the published value of the class of `Q` at a row
  vector `x` lies in `K ⧸ (scalar K).alternatingSubspace = K ⧸ ⊥`. It vanishes if and only
  if `∑ i, ∑ j, x i * Q i j * x j = 0`. The proof rewrites with `quadraticValue_mk`,
  `alternatingSubspace_scalar` and `Submodule.mem_bot`.

## Interpretation: ordinary quadratic forms

The class of `Q ∈ M_n(K)` modulo `{a - ᵗa}` determines the ordinary quadratic form
`x ↦ x Q ᵗx = ∑ i j, x i * Q i j * x j`. Adding `a - ᵗa` does not change it, since
`x a ᵗx = x ᵗa ᵗx`. Conversely, every quadratic form `∑_{i ≤ j} c_{ij} x_i x_j` comes from the
upper triangular matrix with entries `c_{ij}`. A matrix whose quadratic form vanishes is
alternating (zero diagonal and `ᵗQ = -Q`), and every alternating matrix is `a - ᵗa` with `a`
its strictly upper triangular part. So the quotient is in bijection with the ordinary
quadratic forms on `K^n`, in every characteristic. Its polar matrix `Q + ᵗQ` is the Gram
matrix of the polar bilinear form `b_q(x, y) = q(x + y) - q(x) - q(y)`. Nondegeneracy in
the published sense is invertibility of this polar form. In characteristic `2` and odd `n`
this polar matrix is alternating and of odd size, hence never invertible; the statements
that use this module take even `n`. This paragraph is explanatory and is not formalized here
beyond the lemmas above. The isometry group `(scalar K).isometryGroup q` has as points over a
commutative `K`-algebra `R` the units `u` of `R ⊗[K] M_n(K)` with `u Q ᵗu - Q` in
`R ⊗ {a - ᵗa}` (published `mem_range_isometryGroupι_iff`). These are exactly the `u` with
`q(x u) = q(x)` for all row vectors `x` over `R`, that is, the orthogonal group `O(q)`.

## Sources

- J. Tits, *Formes quadratiques, groupes orthogonaux et algèbres de Clifford*, Invent. Math.
  5 (1968), 19–41 (`tits-1968-formes-quadratiques-clifford`), §2.3, printed p. 22 / PDF
  p. 5: "Si `D = k`, d'où `δ = id.`, on posera `Sesq_δ V = Bil V`". For the division algebra
  `D = k` Tits takes the identity involution, which is `scalar K` here. §2.3, printed p. 23 /
  PDF p. 6: "Si `D = k`, on a `D_1 = {0}` d'où `D/D_1 = k`, et l'application `φ` met en
  correspondance bijective l'espace `Q` et l'espace des formes quadratiques sur `V` au sens
  usuel." Here `Q` is Tits's quotient `B/A` of bilinear forms by `{b − π(b)}` (§2.2, printed
  p. 21 / PDF p. 4), which for matrices is `M_n(K) ⧸ {a - ᵗa}`. The map `φ` sends `q` to
  `x ↦ q̄(x, x)`, the value map whose vanishing `scalar_quadraticValue_mk_eq_zero_iff`
  describes.
- The published Markdown of `Langlands.GroupScheme.Quaternionic.Forms` cites J. Tits,
  Bourbaki exposé 505 (1977), 1.1.6, for the general quotient `M_m(D) ⧸ {x - ᵗx^σ}`. The
  scalar involution is the special case `D = K`, `σ = id`.
