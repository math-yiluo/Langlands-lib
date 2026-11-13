# Hyperbolic bases adapted to a hyperbolic pair and to a rank-one torus

Authors: Worker 146.

This internal helper module supports the proof of
`Langlands.GroupScheme.Quaternionic.SpinKernel.SpinKernelGeneratorStatement`
(Task 5870). It refines the hyperbolic bases of
`Langlands.GroupScheme.OrthogonalMatrix.Hyperbolic` in two ways. First, a prescribed
hyperbolic pair can be taken as the first basis pair. Second, there is a weight lemma:
a coordinate change can be chosen so that a one-parameter torus preserving the form
becomes diagonal. Everything is elementary linear algebra over an algebraically closed
field `L` of any characteristic, characteristic `2` included. No outside source is
cited. The arguments are the standard ones (Witt decomposition after splitting off a
given hyperbolic plane, and weight spaces of a torus of an orthogonal group), used
to construct the prescribed adapted coordinates directly.

Matrices act on row vectors from the right. A quadratic form on `n → L` is
`x ↦ x ⬝ᵥ C *ᵥ x` for a matrix `C`, and its polar form is `(x, y) ↦ x ⬝ᵥ (C + Cᵀ) *ᵥ y`.
`IsAlt`, `formMatrix` and `polarMatrix` are those of
`Langlands.GroupScheme.OrthogonalMatrix.Basic`.

## Adapted hyperbolic families

- `exists_adapted_hyperbolicFamily`: let `L` be algebraically closed, let
  `finrank L V = 2 * (k + 1)`, and let `QuadraticMap.polarBilin Q` be nondegenerate.
  Let `x, f` satisfy `Q x = Q f = 0` and `polar Q x f = 1`. Then there is a family
  `v : Fin (k + 1) ⊕ Fin (k + 1) → V` with `Q (v a) = 0`, polar Gram matrix
  `polarMatrix`, `v (inl 0) = x` and `v (inr 0) = f`. The proof is the induction step
  of `exists_hyperbolicFamily_aux`, with the given pair `x, f` in place of the pair
  produced by `exists_hyperbolicPair`. The span `W` of `x, f` has nondegenerate
  restricted form. Its orthogonal `W'` is a complement of dimension `2 k` with
  nondegenerate form. `exists_hyperbolicFamily` on `W'` supplies the remaining vectors.
- `exists_adapted_hyperbolic_matrix` is the matrix form. Let `Q : Matrix n n L` with
  `Q + Qᵀ` invertible and `card n = 2 * (k + 1)`, and let `x, f` be row vectors with
  `x ⬝ᵥ Q *ᵥ x = 0`, `f ⬝ᵥ Q *ᵥ f = 0` and `x ⬝ᵥ (Q + Qᵀ) *ᵥ f = 1`. Then there are
  `P`, `P'` with `P * P' = 1`, `P' * P = 1`, `P * Q * Pᵀ - formMatrix` alternating,
  `P (inl 0) = x`, `P (inr 0) = f`, and `P a ⬝ᵥ (Q + Qᵀ) *ᵥ P b = polarMatrix a b` for
  all rows. The proof repeats that of `exists_hyperbolic_matrix`: `P` has the rows of
  the adapted family, and `P' = (Q + Qᵀ) Pᵀ polarMatrix`.

## The torus element

- `weightMatrix α₁ β₁ α₂ β₂ s s'` is `1 + (s - 1) α₁ β₁ + (s' - 1) α₂ β₂` over any
  commutative ring. Here `αᵢ` are column vectors, `βᵢ` row vectors and `αᵢ βᵢ` is
  `vecMulVec αᵢ βᵢ`.
- `weightMatrix_map`: entrywise ring maps commute with the construction.
- `vecMul_weightMatrix`: `x ᵥ* G = x + ((s - 1)(x ⬝ α₁)) β₁ + ((s' - 1)(x ⬝ α₂)) β₂`.
- `conj_weightMatrix`: suppose `P * P' = 1`, and `P` conjugates `α₁ β₁` and `α₂ β₂` to
  the matrix units at `(i₁, i₁)` and `(i₂, i₂)`. Then `P * G * P'` is
  `1 + single i₁ i₁ (s - 1) + single i₂ i₂ (s' - 1)`.
- Small helpers:
  - `dotProduct_transpose_mulVec_self` and `dotProduct_mulVec_comm`;
  - `IsAlt.dotProduct_mulVec_self` (an alternating matrix has zero quadratic form);
  - `vecMul_dotProduct_mulVec_vecMul`, which says `(x G) C (y G)ᵀ = x (G C Gᵀ) yᵀ`;
  - `vecMulVec_single_one` (the product of two standard basis vectors is a matrix unit).

## The weight lemma

`exists_weight_adapted_matrix`. Let `L` be algebraically closed. Let `C : Matrix n n L`
with `C + Cᵀ` invertible and `card n = 2 * (k + 1)`. Let `α₁, α₂` be column vectors and
`β₁, β₂` row vectors with `βᵢ ⬝ᵥ αⱼ = δᵢⱼ`. Let `s ≠ 0` with `s ^ 2 ≠ 1` be such that
`G = weightMatrix α₁ β₁ α₂ β₂ s s⁻¹` satisfies: `G * C * Gᵀ - C` is alternating. Then
there are `P`, `P'` with the following properties.

- `P * P' = 1` and `P' * P = 1`.
- `P * C * Pᵀ - formMatrix (Fin (k + 1)) L` is alternating.
- `P * vecMulVec α₁ β₁ * P' = single (inl 0) (inl 0) 1`.
- `P * vecMulVec α₂ β₂ * P' = single (inr 0) (inr 0) 1`.

Proof. Write `B(x, y) = x ⬝ (C + Cᵀ) y` and `q(x) = x ⬝ C x`.

1. The alternating hypothesis gives `q(xG) = q(x)` and `B(xG, yG) = B(x, y)`.
2. By `vecMul_weightMatrix`: `β₁ G = s β₁`, `β₂ G = s⁻¹ β₂`, and `w G = w` whenever
   `w ⬝ α₁ = w ⬝ α₂ = 0`.
3. Hence `(s² - 1) q(β₁) = 0` and `(s⁻² - 1) q(β₂) = 0`. So `β₁` and `β₂` are
   isotropic.
4. For such `w`, `(s - 1) B(w, β₁) = 0` and `(s⁻¹ - 1) B(w, β₂) = 0`.
5. Decompose `y = (y ⬝ α₁) β₁ + (y ⬝ α₂) β₂ + w`. With `c = B(β₁, β₂)` this gives
   `B(y, β₂) = (y ⬝ α₁) c` and `B(y, β₁) = (y ⬝ α₂) c`.
6. If `c = 0`, then `(C + Cᵀ) β₁ = 0`. Invertibility gives `β₁ = 0`, contradicting
   `β₁ ⬝ α₁ = 1`.
7. Apply `exists_adapted_hyperbolic_matrix` to the hyperbolic pair `β₁, c⁻¹ β₂`.
8. The polar Gram matrix of the rows of `P` and step 5 give `P α₁ = e_{inl 0}` and
   `P α₂ = c⁻¹ e_{inr 0}`. From `P P' = 1`: `β₁ P' = e_{inl 0}` and
   `β₂ P' = c e_{inr 0}`.
9. Since `P (vecMulVec α β) P' = vecMulVec (P α) (β P')`, the two identities follow.
