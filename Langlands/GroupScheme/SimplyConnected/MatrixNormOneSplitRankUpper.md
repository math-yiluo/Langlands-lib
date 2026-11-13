# Upper bound for the split rank of `SL_m(D)`

Author: Worker 161.

This helper module proves
`Langlands.GroupScheme.MatrixNormOneSplitRank.splitRank_le`. Let `K : Type u` be a field
and `D : Type u` a finite-dimensional central division `K`-algebra. Let `n` be a natural
number with `[NeZero n]`. Then

`splitRank (CentralSimpleUnits.normOne K (Matrix (Fin n) (Fin n) D)) ≤ ((n - 1 : ℕ) : ℕ∞)`.

The field `K` is arbitrary and may be finite. The proof never uses rational points of
`K`. It works with the universal point of the split torus over the group algebra
`K[ℤ^I]`. It does not use the local rank-one classification, local Kneser–Tits, or any
result whose proof consumes this rank computation. The module adds no hypotheses, axioms
or proof holes. All declarations are in the namespace
`Langlands.GroupScheme.MatrixNormOneSplitRank`. It uses the linear algebra of
`Langlands.GroupScheme.SimplyConnected.MatrixNormOneSplitRankAlgebra`.

## Provenance

The lemmas are internal and were written for this proof. The idea is the standard one:
a split torus in `SL_1(A)` diagonalizes `A` by its weight idempotents. The
reduced-norm condition then forces a positive relation among the weights, and each
idempotent of `M_n(D)` uses at least `n · dim D` dimensions.

## Coefficients in `K[Λ] ⊗ A`

For an additive monoid `Λ` and a `K`-algebra `A`:

- `coeffForm m` is the `K`-linear coefficient of the monomial `m` on `K[Λ]`. Here
  `K[Λ]` is `AddMonoidAlgebra K Λ`.
- `coeffTensor A m : K[Λ] ⊗[K] A →ₗ[K] A` sends `p ⊗ x` to `p.coeff m • x`
  (`coeffTensor_tmul`).
- `repr_coeffTensor` says the coordinates of `coeffTensor A m z` in a `K`-basis `b` of
  `A` are the `m`-coefficients of the coordinates of `z` in `b.baseChange`.
  `ext_coeffTensor` deduces that `z` is determined by all of its coefficients.
- `coeffTensor_one_tmul_mul` says that taking coefficients commutes with left
  multiplication by `1 ⊗ x`.

## Weight idempotents of a split torus in `SL_1(A)`

In this section `A : Type u` is a finite-dimensional central simple `K`-algebra. Let
`i : splitTorus (Spec K) I ⟶ normOne K A` be a homomorphism from a split torus with
finite index type `I`. Let `ρ` be the inverse-right-regular representation
`FiniteAlgebraUnits.rightRegularRepresentation (Module.finBasis K A)`. The weights
`weight ρ I (i ≫ normOneι K A) m` and the finite set `weightSupport` come from
`Langlands.GroupScheme.Torus.RingRepresentationWeights`.

- `universalUnit i` is the unit of `K[ℤ^I] ⊗ A` given by the universal torus point
  followed by `i`. It is read through `normOneAffinePointsEquiv`. `universalUnit_eq`
  identifies it with the unit-group point of `i ≫ normOneι K A`.
- `weightElement i m` is the coefficient `e_m := coeffTensor A m (universalUnit i)⁻¹`.
- `weight_mulVec_repr`: the weight matrix `P_m` acts on coordinates as right
  multiplication by `e_m`, that is `P_m *ᵥ repr x = repr (x * e_m)`. The proof applies
  `FiniteAlgebraUnits.affineMatrix_rightRegular_mulVec_repr` to the universal point and
  `y = 1 ⊗ x`. It identifies the affine matrix with `universalMatrix` and takes the
  `m`-coefficient of both sides.
- Consequences, transferred from the weight matrices through coordinates:
  `weightElement_eq_zero` (`e_m = 0` outside the support) and `repr_weightElement`.
  `weightElement_mul` gives `e_m e_{m'} = if m = m' then e_m else 0`, from
  `weight_mul_weight`. `sum_weightElement` gives `∑_{m ∈ support} e_m = 1`, from
  `sum_weight`. `weightElement_ne_zero` gives `e_m ≠ 0` on the support, because
  `P_m ≠ 0` there by `mem_weightSupport`.
- `universalUnit_inv_eq_sum`: `(universalUnit i)⁻¹ = ∑_{m ∈ support} X^m ⊗ e_m`, with
  `X^m = AddMonoidAlgebra.single m 1`. Both sides have the same coefficients.
- `norm_universalUnit_inv`: the regular norm `Algebra.norm K[ℤ^I]` of the inverse
  universal unit is `1`. `Langlands.CentralSimple.norm_eq_reducedNorm_pow` writes the
  norm as a power of the reduced norm, and the inverse of a reduced-norm-one point has
  reduced norm one.
- `sum_finrank_smul_eq_zero` is the weight relation
  `∑_{m ∈ support} dim_K (e_m A) • m = 0` in `ℤ^I`. By `norm_sum_tmul`, the norm of
  `∑ X^m ⊗ e_m` is `X^{∑ dim (e_m A) • m}`. This element equals `1 = X^0`, so the
  exponents agree.
- `closure_weightSupport`: if `IsClosedSubgroup i`, the support generates `ℤ^I` as an
  additive group. Composing the closed immersions `i` and `normOneι`
  (`normOne_isClosedSubgroup`) with the monomorphism `ρ` gives a monomorphism. Then
  `closure_weights_eq_top` applies; it needs `Nontrivial K`, which holds for a field.

## The bound for `M_n(D)`

- `card_le_of_isClosedSubgroup`: for a closed split torus
  `i : splitTorus (Spec K) I ⟶ normOne K (Matrix (Fin n) (Fin n) D)` with `I` finite,
  `Fintype.card I ≤ n - 1`. Put `r_m = dim_K (e_m A)`. Every `r_m` is at least
  `n · dim_K D`, by `le_finrank_range_mulLeft`, so it is positive. With the weight
  relation and `closure_weightSupport`, `card_add_one_le_of_relation` gives
  `card I ≤ |support| - 1`. Also `∑ r_m = dim_K M_n(D) = n · n · dim_K D`, by
  `sum_finrank_piece`. Hence `|support| · (n · dim D) ≤ n · (n · dim D)`, so
  `|support| ≤ n`.
- `splitRank_le` takes the supremum in the definition of `splitRank` over closed split
  tori `𝔾ₘ^I` with `I` finite. It bounds each `Nat.card I` by
  `card_le_of_isClosedSubgroup`.

The module sets `backward.isDefEq.respectTransparency false` and raises
`maxHeartbeats` to `800000` for its elaboration. Neither option changes the statements.
