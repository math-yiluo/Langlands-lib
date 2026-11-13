# Orthogonal bases and hyperbolic coordinates for nondegenerate Hermitian spaces

Author: Worker 166.

This module gives linear coordinates for nondegenerate Hermitian spaces over a
separable quadratic extension `L/K`. It covers any characteristic and makes no
hypothesis on the base field. The fields `K` and `L` share one arbitrary universe,
and the vector space `V` may lie in a different universe. The module also provides a
dictionary between Hermitian matrices on `Index ι` and their pairings on column
vectors. It is linear algebra for Task 5973 and does not prove
`LocalAnisotropicTypeAInnerStatement` or any classification statement.

## Conventions

The pairing `h : V →ₗ[L] V →ₛₗ[bar] L` is linear in the first variable and
conjugate-linear in the second. Here `bar` is the involution of
`SU3Root.fieldInvolution K L`. Hermitian symmetry is the explicit hypothesis
`hbar : ∀ x y, bar (h x y) = h y x`. The published
`DiagonalForm.pairing H x y` is `∑ i, H.weight i * x i * bar (y i)`. The published
`HermitianRoot.gram H` on `Index ι = Unit ⊕ (ι ⊕ Unit)` is the hyperbolic plane
between the top and bottom indices, plus the negative diagonal `-diag(H.weight)`
on the middle indices.

## Orthogonal bases without anisotropy

`exists_pairing_self_ne_zero` assumes the pairing separates points on the left and
`V` is nontrivial, and finds a vector `x` with `h x x ≠ 0`. Suppose instead that
every self-pairing vanishes. Pick a nonzero `x` and a vector `y` with
`h x y ≠ 0`. Let `a` be the conjugate of `traceOne K L / h x y`, where
`SU3Root.traceOne K L` is the published element with `t + bar t = 1`. Expanding
`h (x + a • y) (x + a • y)` with Hermitian symmetry gives `1`. That contradicts the
assumption, and the argument never divides by two.

`exists_orthogonal_basis_of_separatingLeft` uses induction on the dimension to
build a basis `Fin (finrank L V)` that is orthogonal for `h` and has nonzero
self-pairings. At each step it uses the vector from the previous lemma and splits
off the orthogonal complement of its span with Mathlib's
`Sesquilinear.isCompl_span_orthogonal`. The restricted pairing on that complement
again separates points on the left. The basis is assembled with
`Basis.mkFinCons`.

The chosen versions are the definitions `orthogonalBasisOfSeparatingLeft`,
`diagonalFormOfSeparatingLeft` and `diagonalCoordinatesOfSeparatingLeft`. The form
`diagonalFormOfSeparatingLeft` has the self-pairings of the chosen basis as
weights, and `diagonalCoordinatesOfSeparatingLeft` is that basis's `equivFun`.
The lemmas are:

- `_isOrtho`, `_pairing_self_ne_zero` and `_weight_ne_zero`.
- `diagonalFormOfSeparatingLeft_pairing`: the coordinates carry `h` to the
  diagonal pairing, via the published `pairing_eq_diagonal_sum`.

`exists_nondegenerate_diagonal_coordinates` packages these results as an
existence statement. It parallels the published
`exists_anisotropic_diagonal_coordinates`, but assumes only left separation, not
anisotropy, and in exchange concludes only that the weights are nonzero.

## Hyperbolic plus diagonal coordinates

`hyperbolicMiddle_separatingLeft` shows that the middle of a published hyperbolic
splitting (`hyperbolicMiddle`, `hyperbolicCoordinates`) is again left-separating.
`exists_isotropic_diagonal_coordinates` assumes `h.Nondegenerate`, a nonzero
isotropic `x` and `finrank L V = m + 2`. It produces a diagonal form `H` on
`Fin m` with nonzero weights, together with `e : V ≃ₗ[L] L × ((Fin m → L) × L)`,
such that

```
h v w = (e v).1 * bar (e w).2.2
        - H.pairing (e v).2.1 (e w).2.1
        + (e v).2.2 * bar (e w).1.
```

The proof uses the published `exists_hyperbolic_partner`, `hyperbolicCoordinates`,
`hyperbolicCoordinates_pairing` and `negativeMiddlePairing`. It then diagonalizes
the negated middle pairing with `exists_nondegenerate_diagonal_coordinates`. This
generalizes the published `exists_rankOne_diagonal_coordinates`: it does not
require the middle to be anisotropic.

`indexCoordinates A ι : (Index ι → A) ≃ₗ[A] A × ((ι → A) × A)` reads off the top,
middle and bottom coordinates. It has `rfl` simp lemmas and lemmas for standard
basis vectors. `DiagonalForm.pairing_single_single` computes the diagonal pairing
of two standard basis vectors. `exists_isotropic_gram_basis` has the hypotheses of
`exists_isotropic_diagonal_coordinates` and gives `H` with nonzero weights and a
basis `b : Basis (Index (Fin m)) L V` with `h (b i) (b j) = gram H i j` for all
`i, j`. The basis comes from `e` followed by the inverse of `indexCoordinates`.
`gram_apply_comm` states that `gram H` is symmetric.

## Hermitian matrices

The definition `matrixHermitianPairing K M` gives, for a square matrix `M` over `L`,
the pairing `(v, w) ↦ ∑ k, bar (w k) * (M *ᵥ v) k` on column vectors.
`matrixHermitianPairing_apply` unfolds it. The other lemmas are:

- `matrixHermitianPairing_bar`: the pairing is Hermitian when
  `bar (M k l) = M l k`.
- `matrixHermitianPairing_nondegenerate`: the pairing is also nondegenerate when
  `M.det ≠ 0`. Left separation follows by testing against standard basis vectors
  and applying Mathlib's `Matrix.eq_zero_of_mulVec_eq_zero`. Right separation then
  follows from Hermitian symmetry.
- `conjugateTranspose_mul_mul_apply`: for matrices on `Index ι`, the entry `(i, j)`
  of `conjugateTranspose (fieldInvolution K L) P * M * P` is the pairing of column
  `j` of `P` with column `i` of `P`.

## Provenance

This is an internal elementary derivation, not a transcription of a published
theorem. Its inputs are Mathlib's sesquilinear-form and matrix API and the
published Library constructions named above. Orthogonal bases for nondegenerate
Hermitian forms are standard material. The local-field consequences are in
`HermitianLocalIsotropy`.

`indexCoordinates` reuses the existing `indexProductCoordinates` from
`HermitianHyperbolicMatrixCoordinates`, with explicit ring and index arguments.
The top, middle and bottom coordinate maps are unchanged.
