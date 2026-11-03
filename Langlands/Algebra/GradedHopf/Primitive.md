# Homogeneous primitive elements with nonzero differential

Author: Worker 1389 designed and implemented this module and wrote this note, as
part of task `90ffbd89-a3dd-4baa-84ba-332896bbbd17` (split unipotence from the
absence of zero Lie weights). No other worker's draft was reused. It builds on
`Langlands.Algebra.GradedHopf.BigCell`, `InvariantDerivation` and `PolynomialFrobenius`
(same author).

Provenance: internal. These are the algebraic steps that produce, for a unipotent group
with a `𝔾ₘ`-action without zero weights on its Lie algebra, a homogeneous homomorphism to
`𝔾ₐ` that is smooth at the identity. The argument is the author's own implementation, and
no source statement is translated.

## Components of polynomial expressions

`k` is a commutative ring, `A` a commutative `k`-algebra with a `ℤ`-grading `𝒜`.

- `gradeProj_aeval`: if `y j ∈ 𝒜 (w j)` for weights `w : σ → ℤ`, then the degree-`d`
  component of `aeval y f` is `aeval y` of the weighted homogeneous component
  `weightedHomogeneousComponent w d f` (Mathlib). The proof is by induction over
  monomials: `aeval y (monomial m a)` lies in `𝒜 (weight w m)`
  (`SetLike.prod_pow_mem_graded`).
- `totalDegree_weightedHomogeneousComponent_le`: a weighted homogeneous component has
  total degree at most that of the polynomial (its support is smaller).

## Lemma A

Here `k` is a field, `A` a commutative `k`-bialgebra which is a domain, `𝒜` a `ℤ`-grading,
and `z : σ → A` (with `σ` finite) homogeneous polynomial coordinates. That is,
`hzw : ∀ i, z i ∈ 𝒜 (w i)` and `aeval z` is bijective.

- `eq_zero_of_isPrimitiveElem_of_eq_C`: a primitive element whose coordinate polynomial
  is a constant `C c` is zero, since its counit is `c` and also `0`.
- `exists_primitivity_defect`: there is a `k`-linear map `L : A → MvPolynomial (σ ⊕ σ) k`
  such that `L x = 0` iff `x` is primitive, and `L (x ^ p) = L x ^ p` whenever `k` has
  prime characteristic `p`. It is `x ↦ Ψ (comul x - x ⊗ 1 - 1 ⊗ x)`, where
  `Ψ : A ⊗ A ≃ MvPolynomial (σ ⊕ σ) k` combines the coordinate isomorphism with Mathlib's
  `MvPolynomial.tensorEquivSum`. The Frobenius identity is `sub_pow_char` in the
  polynomial ring, together with multiplicativity of `comul`.
- `exists_isPrimitiveElem_not_mem_sq h𝒜 hzw hz`: if `𝒜` is a graded bialgebra
  (`IsGradedBialgebra 𝒜`) and `f ≠ 0` is a primitive element with `f ∈ 𝒜 d`, then there
  are `g` and `d'` with `g ∈ 𝒜 d'`, `g` primitive and `g` not in the square of the
  augmentation ideal `RingHom.ker (Bialgebra.counitAlgHom k A)`.

  Proof (as implemented): strong induction on the total degree `N` of the coordinate
  polynomial `F` of a nonzero homogeneous primitive `f`. If `f` is not in the square,
  take `g = f`. Otherwise all partial derivatives of `F` vanish
  (`pderiv_eq_zero_of_mem_sq`). `N > 0`, since otherwise `F` is constant and `f = 0`.
  - In characteristic `0`, `F` is constant (`eq_C_of_pderiv_eq_zero`), a contradiction.
  - In characteristic `p`, `F = expand p H` and `H = ∑ bⱼ • (Gⱼ).map (frobenius)` with
    `p`-independent `b`. Hence `F = ∑ bⱼ • Gⱼ ^ p` and `f = ∑ bⱼ • gⱼ ^ p` with
    `gⱼ = aeval z Gⱼ`. Applying `L` gives `∑ bⱼ • L(gⱼ) ^ p = L f = 0`, so every `L gⱼ = 0`
    (`eq_zero_of_sum_smul_pow_eq_zero`), i.e. every `gⱼ` is primitive.
  - Some `gⱼ ≠ 0` (else `f = 0`), and some homogeneous component `gradeProj 𝒜 d' gⱼ` is
    nonzero. It is primitive (`IsGradedBialgebra.isPrimitiveElem_gradeProj`). Its
    coordinate polynomial is a weighted homogeneous component of `Gⱼ`. Its total degree
    is at most `deg Gⱼ ≤ deg H < deg H * p = N`, so induction applies.

## A nonzero primitive element from a unitriangular matrix

`exists_isPrimitiveElem_of_unitriangular G hdiag hlow hA`: here `k` is a commutative ring
and `A` a `k`-bialgebra. Let `G : GradedMatrixCoefficients 𝒜` (from `BigCell`) have
diagonal entries `1` (`hdiag`) and zero entries below the diagonal (`hlow : j < i →
M i j = 0`). Suppose some element of `A` is not a scalar (`hA`). Then some entry `M i j`
is nonzero and primitive.

Proof: since the entries generate `A`, some entry is not a scalar. Take one, `M i j`,
with `j - i` minimal. Then `i < j`. The entries `M i l` and `M l j` with `i < l < j` are
scalars, hence equal to their counits, which are `0`. In `comul (M i j) = ∑ₗ M i l ⊗ M l j`
only `l = i` and `l = j` remain, giving `1 ⊗ M i j + M i j ⊗ 1`
(`Bialgebra.isPrimitiveElem_iff_comul_eq_tmul_add_tmul`).
