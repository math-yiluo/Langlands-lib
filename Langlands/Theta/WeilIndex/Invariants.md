# The Weil index and the invariants of a quadratic space

**GKT §3.3.1**: the determinant and the Hasse invariant, **Propositions 3.29** and **3.30** (p. 88).
**GKT Appendix B.2**: **Definition B.28** and **Proposition B.29** (p. 617), for quadratic spaces
the determinant of **Definition B.23** and **Proposition B.24** (p. 616), and the determinant part
of **Proposition B.27** (p. 617).

The module `Langlands.Theta.WeilIndex.Invariants` writes the Weil index `γ(ψ ∘ q)` of a
non-degenerate quadratic space `(V, q)` through its dimension, determinant and Hasse invariant.
A quadratic space is a Mathlib `QuadraticForm F V`, and "non-degenerate" means
`(QuadraticMap.polarBilin q).SeparatingLeft`, as in `OneDimensional.lean`. The book's
`⟨a₁, …, aₙ⟩` is Mathlib's `weightedSumSquares F a`, with `a : Fin n → Fˣ`.

## Content

**Determinant.** Any field with `2 ≠ 0`.

- `diagonalWeights q : Fin (dim V) → Fˣ` is a diagonalization `q ≅ ⟨a₁, …, aₙ⟩`, chosen once
  and for all. If there is none, it is `1`.
- `equivalent_diagonalWeights`: there is one when `2 ≠ 0` and `q` is non-degenerate. This uses
  Mathlib's `equivalent_weightedSumSquares_units_of_nondegenerate'`. Two variants:
  `equivalent_diagonalWeights_of_isometryEquiv` (there is one if `q` has some diagonalization),
  and `finrank_eq_of_isometryEquiv`.
- `quadraticDet q = ∏ aᵢ` is the book's `det(q)`, as a representative in `Fˣ`.
- `exists_prod_eq_quadraticDet_mul_sq` is Proposition B.24 for quadratic spaces: every
  diagonalization has `∏ aᵢ = det(q) u²`. The proof goes through `toMatrix'_weightedSumSquares`
  (the matrix of `⟨a⟩` is `diag(a)`) and Mathlib's `QuadraticForm.discr'_comp`, giving
  `exists_prod_eq_prod_mul_sq`.
- `exists_quadraticDet_eq_mul_sq_of_isometryEquiv`: isometric spaces have the same determinant.
- `exists_quadraticDet_prod` is Proposition B.27 for quadratic spaces:
  `det(V₁ ⊕ V₂) = det V₁ det V₂` in `Fˣ / Fˣ²`. Here `q.prod q'` is Mathlib's orthogonal sum.
- Helpers: `weightedSumSquares_units_apply` and `separatingLeft_polarBilin_weightedSumSquares`.

**Hasse invariant and the Weil index.** A nonarchimedean local field with `2 ≠ 0`. `ψ` is a
non-trivial unitary character.

- `diagonalHasseInvariant a = ∏_{i<j} (aᵢ, aⱼ)_F` (`hilbertSymbol`) and
  `hasseInvariant q = h(q)` are **Definition B.28**.
- `diagonalHasseInvariant_castSucc` and `diagonalHasseInvariant_append` are the two
  combinatorial identities used below. The second is `h(⟨a, b⟩) = h(⟨a⟩) h(⟨b⟩) (∏ aᵢ, ∏ bⱼ)_F`.
- `prod_normalizedWeilIndex`: `∏ γ(aᵢ, ψ) = γ(∏ aᵢ, ψ) ∏_{i<j} (aᵢ, aⱼ)_F`. It follows from
  Proposition 3.19 (b) by induction on `n`, and is the middle step of the book's proof of 3.29.
- `weilIndex_weightedSumSquares` and `weilIndex_eq_of_isometryEquiv_weightedSumSquares` give
  Proposition 3.29 for a given diagonalization:
  `γ(ψ ∘ q) = γ(∏ aᵢ, ψ) γ(ψ)ⁿ ∏_{i<j} (aᵢ, aⱼ)_F`.
- `weilIndex_eq_quadraticDet_hasseInvariant` is **Proposition 3.29**:
  `γ(ψ ∘ q) = γ(det(q), ψ) γ(ψ)ⁿ h(q)`.
- `weilIndex_scale_quadraticForm` is **Proposition 3.30**:
  `γ(ψ_a ∘ q) = (det(q), a)_F γ(a, ψ)ⁿ γ(ψ ∘ q)`. The book's "trivial" equality
  `γ(ψ_a ∘ q) = γ(ψ ∘ a q)` is `weilIndex_scale_eq_smul`.
- `diagonalHasseInvariant_eq_hasseInvariant` is **Proposition B.29 (a)**: every
  diagonalization of `q` gives `h(q)`.
- `hasseInvariant_eq_of_isometryEquiv`: isometric spaces have the same Hasse invariant.
- `hasseInvariant_eq_one_of_isometryEquiv` is **Proposition B.29 (b)**: `h(⟨c, -c⟩) = 1`, and
  `ℍ ≅ ⟨1, -1⟩`.
- `hasseInvariant_prod` is **Proposition B.29 (c)**: `h(V₁ ⊕ V₂) = h(V₁) h(V₂) (det V₁, det V₂)_F`.

**Proof of B.29 (a).** The book calls B.29 (a) and (b) "well-known". Scharlau (Remark 12.5)
derives (a) from Witt's chain equivalence theorem. Here (a) follows from Proposition 3.29:

- Let `⟨b⟩` and `⟨a⟩` be two diagonalizations of `q`. Fix any `ψ`; one exists by
  `nonempty_unitaryAdditiveCharacter`.
- Proposition 3.29 for `⟨b⟩`, computed once directly and once through the isometry `⟨b⟩ ≅ ⟨a⟩`
  (Corollary 3.14), gives
  `γ(∏ bᵢ, ψ) γ(ψ)ⁿ h(⟨b⟩) = γ(∏ aᵢ, ψ) γ(ψ)ⁿ h(⟨a⟩)`.
- `∏ bᵢ = ∏ aᵢ u²` and Proposition 3.19 (a) give `γ(∏ bᵢ, ψ) = γ(∏ aᵢ, ψ)`. This is non-zero,
  so `h(⟨b⟩) = h(⟨a⟩)`.

Parts (b) and (c) then reduce to diagonal forms, as in Scharlau's proof of Lemma 12.6.

The book also says that `dim X`, `det(q)` and `h(q)` determine the isometry class of `q`
(p. 88, Theorem B.33). That classification is not proved here.

## Literature

- W. T. Gan, S. S. Kudla, S. Takeda, *The Local Theta Correspondence* (book draft, 2025):
  §3.3.1, Propositions 3.29 and 3.30, p. 88; Appendix B.2, Definition B.23 and
  Proposition B.24, p. 616; Proposition B.27, Definition B.28 and Proposition B.29, p. 617.
- W. Scharlau, *Quadratic and Hermitian Forms* (Springer, 1985), Chapter 2, §12: Definition 12.4,
  Remark 12.5 and Lemma 12.6, pp. 79–80. This is the book's reference for B.29 (c).

## Declarations

- `Langlands.Theta.weightedSumSquares_units_apply`, `toMatrix'_weightedSumSquares`,
  `separatingLeft_polarBilin_weightedSumSquares`, `exists_prod_eq_prod_mul_sq`.
- `diagonalWeights`, `quadraticDet`, `equivalent_diagonalWeights_of_exists`,
  `equivalent_diagonalWeights`, `finrank_eq_of_isometryEquiv`,
  `equivalent_diagonalWeights_of_isometryEquiv`, `exists_prod_eq_quadraticDet_mul_sq`,
  `exists_quadraticDet_eq_mul_sq_of_isometryEquiv`, `exists_quadraticDet_prod`.
- `diagonalHasseInvariant`, `hasseInvariant`, `diagonalHasseInvariant_castSucc`,
  `diagonalHasseInvariant_append`, `prod_normalizedWeilIndex`, `weilIndex_weightedSumSquares`,
  `weilIndex_eq_of_isometryEquiv_weightedSumSquares`, `weilIndex_eq_quadraticDet_hasseInvariant`,
  `weilIndex_scale_quadraticForm`, `weilIndex_scale_eq_smul`.
- `diagonalHasseInvariant_eq_hasseInvariant`, `hasseInvariant_eq_of_isometryEquiv`,
  `hasseInvariant_eq_one_of_isometryEquiv`, `hasseInvariant_prod`.

Internal declarations, in `Langlands.Theta.WeilIndex.Internal`: `appendLinearEquiv`,
`appendIsometryEquiv` (`⟨a⟩ ⊕ ⟨b⟩ ≅ ⟨a, b⟩`) and `units_int_cast_mul_self`.

## Dependencies

- `Langlands.Theta.WeilIndex.OneDimensional`, and through it the Hilbert symbol
  (`Langlands.ClassFieldTheory.Local.HilbertSymbol`, which gains `hilbertSymbol_prod_left`).
- Mathlib: `LinearAlgebra.QuadraticForm.Prod`.
