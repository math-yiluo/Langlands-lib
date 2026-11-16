# Minors of square matrices

Module `Langlands.LinearAlgebra.MatrixMinor`, namespace `Langlands.Archimedean.MatrixMinor`.

## Role and provenance

This is internal linear-algebra infrastructure with no literature source. All results are
classical facts about determinants. It was written for the reversal step ("Rev") of Task 7069
(Speh's irreducibility criterion for `GL_n(ℝ)`, "if" direction). There the functions
`k ↦ minor k A B` on `O(n)` serve as test vectors. Cauchy–Binet gives their behaviour under
multiplication, and the triangular and complementary-minor results compute their values on
Iwasawa factors. Reindexing along `Fin.castSucc` relates minors of an `n × n` matrix to
minors of a larger matrix that contains it as its upper left block. Nothing in the module is
specific to that use.

## Definition

`minor (X : Matrix (Fin n) (Fin n) R) (A B : Finset (Fin n)) : R`, for a commutative ring `R`.
If `A.card = B.card = k`, it is the determinant of the `k × k` matrix
`(X (a_i) (b_j))_{i,j}`. Here `a_0 < a_1 < … < a_{k-1}` are the elements of `A` and
`b_0 < … < b_{k-1}` those of `B`, listed by `Finset.orderEmbOfFin`. If `A.card ≠ B.card`, the
minor is `0`. Rows and columns are listed in increasing order, so this is the usual minor
`det X_{A,B}` with its usual sign.

## Basic properties

- `minor_eq (hA : A.card = k) (hB : B.card = k)`: the minor is the determinant of
  `X.submatrix (A.orderEmbOfFin hA) (B.orderEmbOfFin hB)`, for any common cardinality `k`.
  This removes the dependence on the particular cardinality proofs in the definition.
- `minor_of_card_ne`: the minor is `0` if `A.card ≠ B.card`.
- `minor_univ`: `minor X univ univ = det X`. The increasing enumeration of `univ` is an
  equivalence `univEquiv n : Fin univ.card ≃ Fin n`, and `det_submatrix_equiv_self` applies.
- `minor_empty`: `minor X ∅ ∅ = 1`, the determinant of a `0 × 0` matrix.
- `minor_congr`: a minor only depends on the entries `X i j` with `i ∈ A` and `j ∈ B`.
- `prod_orderEmbOfFin`: `∏ i, f (s.orderEmbOfFin h i) = ∏ i ∈ s, f i`, by
  `Finset.map_orderEmbOfFin_univ` and `Finset.prod_map`.

## Cauchy–Binet

`minor_mul (hA : A.card = k) (hB : B.card = k)`:

`minor (X * Y) A B = ∑ C ∈ powersetCard k univ, minor X A C * minor Y C B`.

Proof: `(X * Y)_{A,B}` is the product of the `k × n` matrix `X_{A,·}` and the `n × k` matrix
`Y_{·,B}` (`Matrix.submatrix_mul` with the identity in the middle). The Library's rectangular
Cauchy–Binet formula `Langlands.GeneralLinear.Spherical.det_rectangular_mul` (module
`Langlands.Representation.RankinSelberg.FiniteCauchyBinet`) expands its determinant over the
subtype `{C : Finset (Fin n) // C.card = k}`. `Finset.sum_subtype` turns that sum into a sum over
`powersetCard k univ`, and `minor_eq` identifies the terms.

## Transpose, diagonal scaling, identity

- `minor_transpose`: `minor Xᵀ A B = minor X B A`, by `det_transpose`. Both sides are `0` when
  the cardinalities differ.
- `minor_diagonal_mul`: `minor (diagonal a * X) A B = (∏ i ∈ A, a i) * minor X A B`. The
  selected submatrix of `diagonal a * X` is `diagonal (a ∘ enumeration of A)` times that of
  `X`. Then use `det_mul`, `det_diagonal` and `prod_orderEmbOfFin`.
- `minor_mul_diagonal`: `minor (X * diagonal a) A B = minor X A B * ∏ j ∈ B, a j`, from the
  previous item by transposition.
- `minor_one`: `minor 1 A B = if A = B then 1 else 0`. If `A = B`, the submatrix of `1` along
  an injective enumeration is `1` (`Matrix.submatrix_one`). If `A ≠ B` but the cardinalities
  agree, `A` is not contained in `B`. A row indexed by an element `a ∈ A \ B` of the submatrix
  is zero, so the determinant vanishes.
- `minor_diagonal`: `minor (diagonal a) A B = if A = B then ∏ i ∈ A, a i else 0`. Write
  `diagonal a = diagonal a * 1` and combine the two previous items.
- `minor_of_rows_eq_one`: if `X i j = 1 i j` for all `i ∈ A` and all `j` (the rows of `X` in
  `A` are rows of the identity matrix), then `minor X A C = if C = A then 1 else 0` for every
  `C`. By `minor_congr`, the minor equals `minor 1 A C`. No cardinality hypothesis is needed:
  if `C.card ≠ A.card`, both sides are `0`.

## Triangular matrices

- `minor_of_isUpperTriangular (h : X.IsUpperTriangular)`:
  `minor X A A = ∏ i ∈ A, X i i`. `X.IsUpperTriangular` is Mathlib's abbreviation for
  `X.BlockTriangular id`: `X i j = 0` whenever `j < i`. The increasing enumeration of `A` is
  strictly monotone, so the principal submatrix on `A` is upper triangular too. Its
  determinant is the product of its diagonal entries (`det_of_isUpperTriangular`).
- `minor_of_isLowerTriangular (h : X.IsLowerTriangular)`: the same for lower triangular
  matrices (`X i j = 0` whenever `i < j`), by `minor_transpose`.

## Reindexing along an order embedding

- `orderEmbOfFin_map (e : Fin m ↪o Fin n) (A : Finset (Fin m))`: the increasing enumeration
  of `A.map e.toEmbedding` is `i ↦ e (A.orderEmbOfFin h i)`. That map is strictly monotone
  and takes values in `A.map e`, so `Finset.orderEmbOfFin_unique` applies.
- `minor_submatrix_orderEmb (e : Fin m ↪o Fin n) (X : Matrix (Fin n) (Fin n) R)
  (A B : Finset (Fin m))`:
  `minor (X.submatrix e e) A B = minor X (A.map e.toEmbedding) (B.map e.toEmbedding)`.
  If `A.card = B.card`, both sides are determinants of the same `k × k` matrix by the
  previous item. Otherwise both are `0`, since `Finset.map` preserves cardinalities.
- `minor_submatrix_castSucc (X : Matrix (Fin (n + 1)) (Fin (n + 1)) R)`: the case
  `e = Fin.castSuccOrderEmb`,
  `minor (X.submatrix Fin.castSucc Fin.castSucc) A B =
  minor X (A.map Fin.castSuccEmb) (B.map Fin.castSuccEmb)`. The left side is a minor of the
  upper left `n × n` block of `X`.

The module states this only for order embeddings. They keep the increasing order of rows and
columns, so no sign appears.

## Ring homomorphisms and continuity

- `minor_map (f : R →+* S)`: `minor (X.map f) A B = f (minor X A B)`, by `RingHom.map_det`.
- `continuous_minor`: for a topological ring `R`, `X ↦ minor X A B` is continuous on
  `Matrix (Fin n) (Fin n) R`. The determinant and submatrices are continuous; the function is
  constant when the cardinalities differ.

## Jacobi's complementary minor theorem, principal case

- `subtypeEquiv S : Fin S.card ≃ {i // i ∈ S}`, the increasing enumeration of `S`, and
  `minor_eq_det_subtype`: `minor X S S` is the determinant of `X` restricted to the subtype
  `{i // i ∈ S}`.
- `det_eq_minor_compl_of_cols_eq_one`: if the columns of `W` with indices in `S` are columns
  of the identity matrix (`W i j = 1 i j` for all `i` and all `j ∈ S`), then
  `det W = minor W Sᶜ Sᶜ`. Proof: with `b i = decide (i ∉ S) : Bool`, `W` is block triangular
  (`W i j = 0` for `j ∈ S`, `i ∉ S`). By `BlockTriangular.det_fintype`, `det W` is the product
  of the determinants of its two diagonal blocks. The block on `S` is the identity, and the
  block on `Sᶜ` gives `minor W Sᶜ Sᶜ` via `minor_eq_det_subtype`.
- `det_mul_minor_of_mul_eq_one (h : X * Y = 1) (A)`: `det X * minor Y A A = minor X Aᶜ Aᶜ`.
  Proof: let `Z` have the columns of `Y` at indices in `A` and the columns of the identity
  matrix elsewhere. Then `X * Z` has the columns of `X * Y = 1` at indices in `A` and the
  columns of `X` elsewhere. By the previous lemma (for `S = A`),
  `det (X * Z) = minor X Aᶜ Aᶜ`. By the same lemma (for `S = Aᶜ`),
  `det Z = minor Y A A`. Then `det (X * Z) = det X * det Z`.
- `minor_eq_det_mul_minor_compl (h : X * Xᵀ = 1) (A)`: for an orthogonal matrix,
  `minor X A A = det X * minor X Aᶜ Aᶜ`. Apply the previous theorem with `Y = Xᵀ`, and use
  `minor Xᵀ A A = minor X A A` and `det X * det X = det (X * Xᵀ) = 1`.

Only the principal case (equal row and column sets) of Jacobi's theorem is proved. The general
form `det X · minor Y B A = (-1)^(ΣA + ΣB) minor X Aᶜ Bᶜ` for `X * Y = 1` is not part of this
module.
