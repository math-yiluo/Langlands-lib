# Matrix algebras fixed by a twisted Galois action

This internal module proves a Galois descent statement for subalgebras of a
matrix algebra. Let `K/k` be a Galois extension, possibly infinite
(`IsGalois k K`). For each `σ ∈ Gal(K/k)` let `P σ` be an invertible matrix in
`M_n(K)`. A matrix `X` is *twisted fixed* if `P σ · X = σ(X) · P σ` for every
`σ`, where `σ(X)` applies `σ` to every entry. Let `A` be a `k`-subalgebra of
twisted-fixed matrices. The module proves, each under its own hypotheses:

- for any `A` and any invertible `P σ`: `A` is finite-dimensional over `k`;
- if moreover the `K`-span of `A` is `M_n(K)`: `dim_k A = n²`, for any finite
  index type `n` (including the empty one);
- if moreover `n` is nonempty: `A` is simple and central, and `toCSA`
  packages it as a central simple `k`-algebra.

The nonemptiness of `n` is essential: for `n` empty, `M_n(K)` is the zero ring,
which is not a simple ring. Since a `k`-basis of `A` is then a `K`-basis of
`M_n(K)` (see `finrank_eq`), the scalar-extension map `K ⊗_k A → M_n(K)` is
an isomorphism.

The motivation is the descent step in the proof of Theorem 3.3 of Tits,
*Représentations linéaires irréductibles d'un groupe réductif sur un corps
quelconque*, J. reine angew. Math. 247 (1971), pp. 203–204. There, twisting by
a projective cocycle `ζ` lifted to matrices `U_σ` sends `X` to
`U_σ σ(X) U_σ⁻¹`. Its fixed equation is the twisted-fixed equation above with
`P σ = U_σ⁻¹`. In the application, `P σ` intertwines a representation `ρ`
with its Galois twist. The matrix statements here are internal lemmas; the
linear-independence argument is the classical one behind Speiser's lemma.

## Declarations

- `twistedFixed P` is the `k`-subalgebra of `M_n(K)` of twisted-fixed matrices.
  It is closed under sums and products because `σ` acts on entries as a ring
  map. It contains the scalars from `k` because `σ` fixes `k`.
- `map_linearCombination_conjugate` is a bookkeeping identity: applying `σ` to
  a `K`-linear combination of matrices conjugates its coefficients and the
  matrices. It is proved by induction on finitely supported coefficient
  vectors.
- `linearIndependent_of_le_twistedFixed`: a family of twisted-fixed matrices
  that is linearly independent over `k` is linearly independent over `K`.
  The proof considers the `K`-subspace `W` of coefficient vectors `c` with
  `Σ c_i v_i = 0`. Then `W` is stable under conjugating coefficients by any
  `σ`. To see this, multiply the conjugated relation on the left by `P σ`,
  use the twisted-fixed identity, and cancel the unit `P σ`. By the published
  `GaloisSubmoduleDescent.eq_span_ground_vectors` (valid for infinite Galois
  extensions), `W` is spanned by vectors with coefficients in `k`. These are
  `k`-relations, so they are zero.
- `linearIndepOn_of_le` is the same statement for sets of matrices.
  `mem_of_mem_span` follows from it: an element of `A` lying in the `K`-span
  of a `k`-subspace `V ⊆ A` already lies in `V`. Otherwise `V` would have a
  `k`-basis that stays independent over `K` after adding the element.
- `finiteDimensional`: `A` is finite-dimensional over `k`. Every `k`-independent
  finite family in `A` is `K`-independent in `M_n(K)`, so it has at most `n²`
  elements (Mathlib's `rank_le`).
- `commute_of_forall_commute`, `mul_mem_span_left` and `mul_mem_span_right`
  use only that the `K`-span of `A` is `M_n(K)`. A matrix commuting with `A`
  commutes with everything. The `K`-span of a `k`-subspace of `A` stable
  under left (respectively right) multiplication by `A` is stable under left
  (respectively right) multiplication by all matrices.
- `isSimpleRing` (for `n` nonempty): let `I` be a nonzero two-sided ideal of
  `A`. The `K`-span of `I` is a nonzero two-sided ideal of the simple ring
  `M_n(K)`, so it contains `1`. Then `mem_of_mem_span` gives `1 ∈ I`.
- `isCentral` (for `n` nonempty): a central element `z` of `A` commutes with all
  matrices, so it is a scalar `c` (Mathlib's `Matrix.center_eq_scalar_image`).
  The twisted-fixed identity and invertibility of `P σ` give `σ(c) = c` for
  all `σ`. So `c ∈ k` by Mathlib's `InfiniteGalois.mem_range_algebraMap_iff_fixed`.
- `finrank_eq` (for any finite `n`, under the spanning hypothesis):
  `dim_k A = n²`. A `k`-basis of `A` is `K`-independent and spans `M_n(K)`
  over `K`, hence it is a `K`-basis of `M_n(K)`.
- `toCSA` (for `n` nonempty, `K/k` Galois, invertible `P σ`, `A` twisted
  fixed with `K`-span `M_n(K)`) packages `A` as an element of Mathlib's
  `CSA k`, the type of finite-dimensional central simple `k`-algebras used to
  define `BrauerGroup k`. `toCSA_carrier` records that its carrier is `A`.

No continuity hypothesis on `σ ↦ P σ` and no finiteness of `K/k` is needed.
Only the conjugation identity on `A` and the invertibility of each `P σ` are
used.
