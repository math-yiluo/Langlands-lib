# Invariant integration for reductive groups in characteristic zero

This module is internal supporting work. It contains no source-cited definition. Assuming
characteristic-zero complete reducibility, `ReductiveCharZeroSemisimplicityStatement`, it builds
a normalized invariant integral on the actual coordinate algebra of every connected reductive
group over a characteristic-zero field. The complete-reducibility statement stays an explicit
hypothesis of every result that uses it. No Levi decomposition is used.

The mathematical background is the Reynolds operator of a linearly reductive group (Milne,
*Algebraic Groups*, registered source `milne-2022-algebraic-groups`, Reynolds-operator
paragraph, printed p.249). The Lean route below is internal: it avoids infinite-dimensional
representations by working with finite sets of coordinates and gluing.

## Local integrals in a bialgebra

Let `B` be a bialgebra over a field `K` with comultiplication `y ↦ ∑ y₁ ⊗ y₂`. `rightAct l y` is
`∑ y₁ · l(y₂)` and `leftAct r y` is `∑ r(y₁) · y₂` (published in
`AffineLinearEmbedding.Comodule`).

- `IsLeftIntegralAt l y` means `rightAct l y = l(y) • 1`.
- `IsRightIntegralAt r y` means `leftAct r y = r(y) • 1`.
- `eq_of_isLeftIntegralAt_of_isRightIntegralAt` (Fubini): if `l(1) = r(1) = 1`, `l` is a left
  integral at `y` and `r` is a right integral at `y`, then `l(y) = r(y)`. Both values equal
  `∑ r(y₁) l(y₂)`, by the published `apply_leftAct`.
- `map_rightAct_comp`: suppose `S` is linear and `comul (S y) = (S ⊗ S)(swap (comul y))`. Then
  `S (rightAct (r ∘ S) y) = leftAct r (S y)`. The proof is induction over tensors.
- `isLeftIntegralAt_comp`: if moreover `S` is an involutive algebra map and `r` is a right
  integral at `S y`, then `r ∘ S` is a left integral at `y`.
- `exists_left_integral` (gluing) has two hypotheses. Every `y` must have a normalized right
  integral at `y`. Every finite set `T` must have a normalized functional `L_T` that is a left
  integral at every element of `T`. The conclusion is a normalized functional `ℓ` that is a left
  integral at every element.
  - Fubini makes the values `L_T(z)`, for `z ∈ T`, independent of `T`. So
    `ℓ(z) := L_{{z}}(z)` is linear: compare with `L_{{x, y, x + y}}` and `L_{{x, c • x}}`.
  - For `z`, write `comul z` as a finite sum `∑ aᵢ ⊗ bᵢ` (`TensorProduct.exists_finset`). On
    `T = {z} ∪ {bᵢ}`, `ℓ` agrees with `L_T`. Hence `rightAct ℓ z = rightAct L_T z = L_T(z) • 1`,
    which equals `ℓ(z) • 1`.

## The antipode of a corepresented group functor

Let `e` corepresent a group-valued functor `F` on commutative `R`-algebras by `B`. Then
The existing `(Corepresented.antipode e).hom : B →ₐ[R] B` classifies the inverse of the universal point.

- `pt_comp_antipode`: composing with the antipode inverts classified points.
- `antipode_antipode`: the antipode is involutive.
- `comul_comp_antipode`: `comul ∘ S = (S ⊗ S) ∘ swap ∘ comul`, as algebra maps. Points satisfy
  `(xy)⁻¹ = y⁻¹x⁻¹`.

## Local integrals for connected reductive groups

Fix a field `k` of characteristic zero and a connected reductive `H` over `Spec k` with affine
structure morphism. Let `B = Lie.coordinateAlgebra H`, with the bialgebra structure of the
corepresentation `e = corepresentableBy H (Lie.coordinateIso H)` of its affine point functor.
Write `hss` for the complete-reducibility hypothesis.

- `exists_right_integral hss hH T`: for every finite `T ⊆ B` there is `r` with `r(1) = 1` that is
  a right integral at every element of `T`. The proof:
  1. Let `V` be the published `Chevalley.regularSpan (T ∪ {1})`. It is finite-dimensional and
     stable under every `rightAct`. Choose a basis `b`, with coordinate functionals
     `extendedCoord`. `ρ` is the published regular representation of the corepresented group
     scheme on `V`, with universal matrix `M = subspaceMatrix V b`.
  2. The coordinates `u` of `1` satisfy `∑ⱼ u_j M_{ij} = u_i • 1`, because
     `leftAct f 1 = f(1) • 1`. At the universal point this says `ρ` fixes `u`. Also `u ≠ 0`.
  3. Restrict `ρ` to `H` along the inverse of the published `modelIso`. The vector `u` is still
     fixed, so `MatrixRepresentation.exists_dual_fixed_of_semisimplicity` (module
     `Reductive.CharZeroDualFixedDescent`) gives `c` fixed by the dual with `c · u = 1`.
     Restricting back along `modelIso.hom` and evaluating at the universal point gives
     `∑ᵢ cᵢ M_{ij} = c_j • 1`.
  4. Put `r = ∑ᵢ cᵢ · extendedCoord i`. Then `r(b_j) = c_j` and `r(1) = c · u = 1`. The published
     `comul_basis` gives `leftAct r (b_j) = ∑ᵢ cᵢ M_{ij} = c_j • 1`. By linearity over
     `basis_expand`, `r` is a right integral at every element of `V`, in particular of `T`.
- `exists_left_integral_finset hss hH T`: apply `exists_right_integral` to the image of `T` under
  the antipode, then compose with the antipode (`isLeftIntegralAt_comp`).
- `exists_left_integral_of_semisimplicity hss hH`: there is `ℓ` with `ℓ(1) = 1` that is a left
  integral at every coordinate. The two previous results feed `exists_left_integral`.
- `coordinateCoproduct_eq_comul`: the coproduct `CoordinateIntegration.coordinateCoproduct H`
  induced by actual multiplication equals `comul e`. Both classify the product of the two
  universal points over `B ⊗ B`; the proof uses `leftTranslation_universalPoint` and
  `pointCoordinates_naturality`.
- `contract_comul`: `CoordinateIntegration.contract H B ℓ (comul z) = rightAct ℓ z`.

## Main results

- `invariantIntegralOfSemisimplicity hss H hH : CoordinateIntegration.InvariantIntegral H` is the
  glued left integral, packaged by `InvariantIntegral.ofCoordinateCoproduct`. Its coproduct
  identity is `rightAct ℓ z = ℓ(z) • 1`, rewritten with the two comparison lemmas.
- `characteristicZeroReductiveInvariantIntegral_of_semisimplicity`:
  `ReductiveCharZeroSemisimplicityStatement.{u} →
  CharacteristicZeroReductiveInvariantIntegralStatement.{u}`.
- `characteristicZeroReductiveVectorExtension_of_semisimplicity`:
  `ReductiveCharZeroSemisimplicityStatement.{u} →
  CharacteristicZeroReductiveVectorExtensionStatement.{u}`, by composition with the published
  `characteristicZeroReductiveVectorExtension_of_invariantIntegral`.

These are conditional results. They do not prove complete reducibility.
