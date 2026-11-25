# The determinant of an `ε`-Hermitian space

**GKT §4.5.1**: the determinant (4.12) of a non-degenerate `ε`-Hermitian space, the norm map (4.13),
**Lemma 4.34** (second assertion) (pp. 122–123); the computation behind **Lemma 4.29** (p. 116).

The module `Langlands.LinearAlgebra.EpsilonHermitian.Determinant` treats a commutative `D = E`: a
field `K` with an involution `τ` (`τ = id` gives `D = E = F`, `ε`-symmetric forms; `τ ≠ id` gives a
quadratic extension `E/F`, Hermitian and skew-Hermitian forms), so that the reduced norm of §4.1.2 is
the determinant and `r = 1`. The quaternionic case is not treated.

## Content

- In `Langlands.RingInvo`: `conjRingHom τ : K →+* K` (`d ↦ d^τ` is a ring endomorphism of a field),
  `normHom τ : Kˣ →* Kˣ`, `a ↦ a a^τ` (the book's `𝒩_{E/F}`, (4.13): the norm for `[E : F] = 2`,
  the square for `τ = id`), `normSubgroup τ` its range, `mk_normHom`, `mk_map_conj`
  (`a^τ ≡ a⁻¹` modulo norms), `mk_eq_mk_of_coe_eq_mul_norm`.
- `gramMatrix k b`, the matrix `(k (bᵢ) (bⱼ))` of (4.12); `gramMatrix_eq_mul` and
  `det_gramMatrix_eq` (change of basis: `G' = Mᵀ G M^τ`, so `det G' = det M · (det M)^τ · det G`);
  `det_gramMatrix_ne_zero` (non-degenerate forms have invertible Gram matrices);
  `gramMatrix_map_conj : G^τ = ε Gᵀ`.
- **Lemma 4.34** (second assertion, `r = 1`): `conj_det_gramMatrix : det(G)^τ = ε^n det(G)`.
- `detUnit hk b : Kˣ` and `det hk : Kˣ ⧸ normSubgroup τ`, the book's `det(ρ)` (computed in
  `Module.finBasis`); `det_eq_mk` (every basis gives the same class) and
  `IsometryEquiv.det_eq` (isometric spaces have the same determinant; so `det` is defined on
  isometry classes, as Definition 4.33 needs).
- `det_mul_conj_det_eq_one`: if `f : A → A` and `f' : B → B` preserve a `τ`-sesquilinear pairing
  `β : A × B → K` that is non-degenerate on the left, with `dim A = dim B`, then
  `det f' · (det f)^τ = 1`. With `β = h|_{X × Y}` this is Lemma 4.29 (`det(a^∨) = (det a)^{-τ}`), and
  with the pairing induced on `X/(X ∩ gX) × gX/(X ∩ gX)` it is the heart of Lemma 4.35 (both in
  `Theta/Metaplectic/RaoFunction.lean`). The proof compares Gram matrices: `P = Aᵀ P B^τ`.

## Conventions

The form is linear in the first variable and `τ`-semilinear in the second (left spaces,
`Basic.lean`), so the Gram matrix of a basis `b` is the same matrix as the book's for the same
vectors of the right space `W`, and `det(ρ)` is convention-free. Endomorphism matrices, however, are
`τ` of the book's (Proposition B.6), see `RaoFunction.md`.

## Literature

- W. T. Gan, S. S. Kudla, S. Takeda, *The Local Theta Correspondence* (book draft, 2025): §4.1.2
  (Lemma 4.2), pp. 95–96; Lemma 4.29, p. 116; §4.5.1, (4.12), (4.13), Definition 4.33 and
  Lemma 4.34, pp. 122–123.

## Declarations

In `Langlands.RingInvo`: `conjRingHom`, `conjRingHom_apply`, `normHom`, `coe_normHom`,
`normSubgroup`, `normHom_mem`, `mk_normHom`, `mk_map_conj`, `mk_eq_mk_of_coe_eq_mul_norm`.

In `Langlands.EpsilonHermitianForm`: `gramMatrix`, `gramMatrix_apply`, `gramMatrix_eq_mul`,
`det_gramMatrix_eq`, `det_gramMatrix_ne_zero`, `gramMatrix_map_conj`, `conj_det_gramMatrix`,
`detUnit`, `coe_detUnit`, `det`, `det_eq_mk`, `IsometryEquiv.det_eq`, `det_mul_conj_det_eq_one`.

Private: `mk_detUnit_eq_of_reindex`.

## Dependencies

- `Langlands.LinearAlgebra.EpsilonHermitian.Basic`.
- Mathlib: `LinearAlgebra.Matrix.ToLinearEquiv`, `LinearAlgebra.Matrix.Basis`,
  `LinearAlgebra.Determinant`, `GroupTheory.QuotientGroup.Basic`.
