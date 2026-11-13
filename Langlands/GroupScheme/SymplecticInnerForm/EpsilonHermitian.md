# `ε`-symmetric elements of algebras with involution

Author: Worker 74, for Task 6243 (`d75aa284-b911-411c-8e33-34184b737113`). This module is
linear-algebra support for the proof of
`Langlands.GroupScheme.SymplecticInvolutionAntihermitianStatement` in
`SymplecticInnerForm/SymplecticInvolutionAntihermitian`. All declarations live in the
namespace `Langlands.GroupScheme.Quaternionic.FirstKindInvolution` and concern an involution
of the first kind `θ : FirstKindInvolution K R` (published in `Quaternionic/Involution`: a
`K`-linear map `R → R` with `θ 1 = 1`, `θ (x * y) = θ y * θ x` and `θ (θ x) = x`).

## Definitions

- `epsSymmetric θ ε : Submodule K R`, for a scalar `ε : K`, is the kernel of
  `θ - ε • id`, that is `{x | θ x = ε • x}` (`mem_epsSymmetric`). For `ε = 1` it is the
  published `symmetricSubspace` (`epsSymmetric_one`); for `ε = -1` it is the space of skew
  elements.
- `algEquivCongr θ φ`, for a `K`-algebra isomorphism `φ : R ≃ₐ[K] B`, is the transported
  involution `x ↦ φ (θ (φ⁻¹ x))` of `B` (`algEquivCongr_apply`, `algEquivCongr_apply_map`).
- `epsSymmetricCongr θ φ ε` restricts `φ` to a `K`-linear equivalence from the
  `ε`-symmetric elements of `θ` to those of `algEquivCongr θ φ`.
- `gramEquiv θ τ hε hHH' hH'H hθH hτ` is a `K`-linear equivalence
  `θ.epsSymmetric ε ≃ₗ[K] τ.symmetricSubspace`, `z ↦ H * z`, under the hypotheses
  `ε * ε = 1`, `H * H' = 1`, `H' * H = 1`, `θ H = ε • H` and `τ y = H * θ y * H'` for all `y`
  (so `τ = Int(H) ∘ θ`). The inverse is `y ↦ H' * y`.
- `hermCoordEquiv θ ι hε`, for a finite linearly ordered index type `ι` and `ε * ε = 1`, is a
  `K`-linear equivalence between the `ε`-hermitian matrices `{z | ᵗz^θ = ε • z}`
  (the `ε`-symmetric elements of the published conjugate-transpose involution
  `θ.matrix ι`, with `(θ.matrix ι z) i j = θ (z j i)`) and the product of
  `ι → θ.epsSymmetric ε` (the diagonal) with `{p : ι × ι // p.1 < p.2} → R` (the strictly
  upper triangular entries).

## Theorems

- `map_gram_inv`: if `ε * ε = 1`, `H * H' = 1` and `θ H = ε • H`, then `θ H' = ε • H'`.
  Proof: applying `θ` to `H * H' = 1` gives `θ H' * θ H = 1`, so `ε • (θ H' * H) = 1`;
  multiplying on the right by `H'` gives `ε • θ H' = H'`, and multiplying by `ε` gives the
  claim.
- `finrank_symmetricSubspace_eq_of_gram` (for `R` free and finite over `K`): with the
  hypotheses of `gramEquiv`, `finrank K τ.symmetricSubspace = finrank K (θ.epsSymmetric ε)`.
  It is the dimension equality of `gramEquiv`. The membership checks in `gramEquiv` are:
  if `θ z = ε • z` then `τ (H z) = H θ(z) θ(H) H' = ε² H z H H' = H z`; conversely, if
  `τ y = y` then `θ (H' y) = θ y θ H' = ε • θ y H'`, and `θ y H' = H' (H θ y H') = H' y`.
- `finrank_epsSymmetric_matrix` (for `K` a field, `R` finite-dimensional, `ι` finite with
  decidable equality, `ε * ε = 1`):
  `finrank K ((θ.matrix ι).epsSymmetric ε) =
    card ι * finrank K (θ.epsSymmetric ε) + (card ι).choose 2 * finrank K R`.
  Proof: choose the linear order on `ι` transported from `Fintype.equivFin`, apply
  `hermCoordEquiv`, and count. The number of pairs `i < j` is `(card ι).choose 2`
  (`Fintype.card_product_filter_lt`). In `hermCoordEquiv`, an `ε`-hermitian matrix is
  determined by its diagonal and its strictly upper part, because `z j i = ε • θ (z i j)`
  (using `ε * ε = 1`). Conversely, every choice of `ε`-symmetric diagonal and arbitrary
  upper part is realized by the matrix with entries `st.2 (i, j)` above the diagonal and
  `ε • θ (st.2 (j, i))` below it.
- `finrank_symmetricSubspace_add_finrank_skew` (for `K` a field with `(2 : K) ≠ 0` and `R`
  finite-dimensional): `finrank K θ.symmetricSubspace + finrank K (θ.epsSymmetric (-1)) =
  finrank K R`. Proof: the two subspaces meet in `0`, since `x = θ x = -x` gives `2 • x = 0`.
  They span, since `x = 2⁻¹ • (x + θ x) + 2⁻¹ • (x - θ x)`. Then apply
  `Submodule.finrank_sup_add_finrank_inf_eq`.

## Provenance

Provenance: derived (elementary linear algebra). The source is M.-A. Knus, A. Merkurjev,
M. Rost and J.-P. Tignol, *The Book of Involutions* (AMS Colloquium Publications 44, 1998;
source `knus-merkurjev-rost-tignol-1998-book-of-involutions`):

- `gramEquiv` is the identity `Sym(A, Int(u) ∘ σ) = u · Sym(A, σ)` for `σ(u) = u`, and
  `= u · Skew(A, σ)` for `σ(u) = -u`, of Proposition (2.7)(2), printed p.17 (PDF p.40).
  The Lean version allows any scalar `ε` with `ε * ε = 1` and any `K`-algebra `R`.
- The decomposition `A = Sym(A, σ) ⊕ Skew(A, σ)` away from characteristic two is used in the
  discussion before Definition (2.5), printed p.16 (PDF p.39).

The count of `ε`-hermitian matrices by diagonal and upper triangular entries is elementary;
KMRT does not state it in this form. The Lean proofs are self-contained.
