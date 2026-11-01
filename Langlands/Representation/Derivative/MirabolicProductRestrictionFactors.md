# Tensor factors and characters for the mirabolic restriction sequence

Author: Worker 1163.

This helper module of the proof of
`Langlands.Derivative.MirabolicProductRestrictionStatement` identifies the block
tensor of the binary shape with the binary tensor product, and the positive half
of the binary block modulus, on the two orbit stabilizers, with the published
mixed-product characters. These are internal computations with no separate
literature source; they correspond to the comparison of characters in
Bernstein–Zelevinsky (1977), §7.1 (via §6.5), printed p.471.

## Tensor factors

In namespace `Langlands.FiniteTensor`, for `V : Fin 2 → Type`:

- `binaryLinearEquiv R V : PiTensorProduct R V ≃ₗ V 0 ⊗ V 1` is the published
  `headTailLinearEquiv` followed by the published singleton equivalence on the
  tail; `binaryLinearEquiv_tprod` gives `⨂ v ↦ v 0 ⊗ v 1`.
- `binaryLinearEquiv_external`: for representations `ρ i` of groups `H i`, the
  published external action `external ρ g` corresponds to
  `TensorProduct.map (ρ 0 (g 0)) (ρ 1 (g 1))`.
- `binaryLinearEquiv_externalMap`: the published `externalMap f` corresponds to
  `TensorProduct.map (f 0) (f 1)`.

All three are proved on pure tensors by `PiTensorProduct.induction_on`.

## Determinants and characters

In namespace `Langlands.Derivative.MirabolicProductRestriction`:

- `determinantNorm_mirabolic` gives the determinant-norm equality for the
  published `Mirabolic.projection`. It reuses
  `GeneralLinear.Mirabolic.determinant_projection` from
  [MirabolicModularCharacterProof](../../Group/GL/MirabolicModularCharacterProof.md),
  whose Laplace expansion along the last row proves the determinant equality.
- `leviModulus_shape`: for the binary shape, the published
  `T.leviModulus (shape m n) x` equals `ν(x₀)^(n+1) / ν(x₁)^(m+1)`, where
  `ν = T.determinantNorm`; the published product formula has the single pair of
  blocks `0 < 1`.
- `leviHalfModulus_eq_leftLeviCharacter`: if `x₁` is the mirabolic element
  `q ∈ P_(n+1)`, then `δ^(1/2)(x) = √(ν(x₀)^(n+1) / ν(q)^(m+1))` equals the
  published case (II) character
  `leftLeviCharacter (m+1) n (x₀, q) = ν(x₀)^((n+1)/2) ν(q)^(-(m+1)/2)`.
- `leviHalfModulus_eq_rightLeviCharacter`: if `x₀` is the mirabolic element
  `q ∈ P_(m+1)`, then `δ^(1/2)(x)` equals the published case (III) character
  `rightLeviCharacter (n+1) m (q, x₁) = ν(proj q)^((n+1)/2) ν(x₁)^(-(m+1)/2)`,
  using `ν(q) = ν(proj q)`. In the published definition this character is the
  rectangle half-power times the case (III) factor `ε = ν(x₁)^(-1/2)`
  (`rightLeviCharacter_eq_mul`), so the retained `ε` is exactly accounted for
  by `δ^(1/2)` of the binary parabolic; no further twist occurs.

The real-power identity `√(x^a / y^b) = x^(a/2) y^(-b/2)` for positive `x, y` is
the private `sqrt_div_pow`.

## Imports

`Tensor.FiniteEquivalences`, `Mirabolic.MixedProducts` (the characters) and the
orbit module `Derivative.MirabolicProductRestrictionOrbits` (for `shape`).
