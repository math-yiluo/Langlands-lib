# Definite signatures give positive involutions

Author: Worker 19.

Let `σ` be an involution of the second kind on an algebra `A` over a CM
field `K` with totally real subfield `E`. Suppose `σ` has the definite
signature `(n, 0)` at every real embedding of `E`, as expressed by the
published predicate `HasDefiniteSignature σ n` of Worker 57. This module
proves that the restriction of `σ` to `ℚ` becomes a positive involution after
extending scalars to `ℝ`. This is the positivity hypothesis used by
`PositiveArithmeticFinite` and the modules built on it, now derived for
Harris's definite group.

## Source

Harris (1999), Section 1, printed p. 301 (PDF p. 3): `J = U(𝒟, *)`,
`GJ = GU(𝒟, *)`, and among the hypotheses following (1.1),
"`J_∞ = ∏_{σ ∈ Σ_E} U(n)`". So the unitary group of `(𝒟, *)` is compact at
every real place of `E`. The published `HasDefiniteSignature` expresses
this algebraically. At every real embedding `τ` it requires a real algebra
isomorphism `ℝ ⊗_{E,τ} A ≃ M_n(ℂ)` carrying `σ ⊗ ℝ` to the adjoint for the
Hermitian form of signature `(n, 0)`.

Positivity is the published `AlgebraInvolution.IsPositive` (Worker 57,
`Positivity`). It follows Milne, *Introduction to Shimura varieties*,
Proposition 8.10(c) and Definition 8.11: `Tr_{C/ℝ}(c* c) > 0` for every
nonzero `c`.

## Setting

- `E` is a totally real number field, `K` a totally complex quadratic
  extension, and `A` a ring with `E`-, `K`- and `ℚ`-algebra structures and
  `IsScalarTower ℚ E A`. `σ : SecondKindInvolution E K A`, and
  `σ.rationalInvolution` is its restriction to `ℚ` (published, `CMData`).
- `signatureMatrix n r`, `signatureAdjoint n r`, `HasSignature` and
  `HasDefiniteSignature` are published in `Signature`. `piConjTranspose n I`
  is conjugate transposition on `I → M_n(ℂ)` (published, `Positivity`).
- `Global.TotallyReal.algebraEquiv E A b` is the published real splitting
  `ℝ ⊗_ℚ A ≃ ∏_{τ : E → ℝ} ℝ ⊗_{E,τ} A` for a finite `E`-basis `b` of `A`
  (`RealAlgebraSplitting`).

## Declarations

- `signatureMatrix_self`: `signatureMatrix n n = 1`, since every diagonal
  index is below `n`.
- `signatureAdjoint_self_apply`: `signatureAdjoint n n x = star x`. The
  adjoint is `x ↦ J⁻¹ x* J` with `J = signatureMatrix n n = 1`.
- `SecondKindInvolution.definiteMatrixEquiv b h`: for
  `h : HasDefiniteSignature σ n`, the composite
  `ℝ ⊗_ℚ A ≃ ∏_τ ℝ ⊗_{E,τ} A ≃ ∏_τ M_n(ℂ)` of the published real splitting
  with the charts chosen from `h` at each `τ`.
- `SecondKindInvolution.definiteMatrixEquiv_involution`: this isomorphism
  carries `σ.rationalInvolution.baseChange ℝ` to `piConjTranspose`. On a pure
  tensor `r ⊗ a`, the component at `τ` is the chart applied to `r ⊗ a`. The
  chart identity of `h` and `signatureAdjoint_self_apply` give conjugate
  transposition. The general case follows by additivity.
- `SecondKindInvolution.isPositive_of_hasDefiniteSignature`: if `A` is
  finite over `E` and `HasDefiniteSignature σ n` holds, then
  `(σ.rationalInvolution.baseChange ℝ).IsPositive`. Positivity transfers
  along involution-compatible algebra isomorphisms (the published
  `isPositive_iff_of_algEquiv`), and `piConjTranspose` is positive (the
  published `piConjTranspose_isPositive`). The basis used is Mathlib's
  `Module.finBasis E A`.

## Scope

- **From the signature predicate, not from the group.** The input is the
  published `HasDefiniteSignature`, an algebraic form of
  `J_∞ ≅ ∏ U(n)`. Deriving it from compactness of the real unitary group is
  not done.
- **Only positivity.** The module does not combine this with the finiteness
  and small-level results (`PositiveArithmeticFinite`, `HarrisSmallLevels`),
  which are separate candidates.

## Provenance

The source is Harris (1999), Section 1, printed p. 301, read in the original
(rendered page), through Worker 57's published `HasDefiniteSignature`. The
positivity predicate and its transport lemma are Worker 57's published
`Positivity` and `RealPositivity`. The identification of the definite
adjoint with conjugate transposition and the assembly are written for this
module.

Source IDs and SHA-256 fingerprints:

- `harris-1999-cohomological-automorphic-forms-525a222c4489ee9d`:
  `525a222c4489ee9d3fe86a52c6c17ffb30fcc7c31f24c16a64669e9615085b26`.
- `arthur-ellwood-kottwitz-2005-harmonic-analysis-shimura` (Milne's
  notes, through the published `Positivity`):
  `88ba9a23fa62e2f62f14af7a5a2a8ffb062be29fc4590bf39c60c173add0a8a7`.

Formal dependencies:

- the published `Langlands.Global.RealAlgebraSplitting`
  (`Global.TotallyReal.algebraEquiv`, `algebraEquiv_tmul`);
- the published `Langlands.Shimura.Unitary.RealPositivity`
  (`AlgebraInvolution.isPositive_iff_of_algEquiv`) and, through it,
  `Positivity` (`IsPositive`, `piConjTranspose`, `piConjTranspose_apply`,
  `piConjTranspose_isPositive`);
- the published `Langlands.Shimura.Unitary.Signature` (`signatureMatrix`,
  `signatureAdjoint`, `HasSignature`, `HasDefiniteSignature`) and `CMData`
  (`SecondKindInvolution`, `rationalInvolution`);
- Mathlib `5ed2965256430c3649e86755f9576b54eca72435` under Lean 4.34.0, in
  particular `AlgEquiv.piCongrRight`, `TensorProduct.inductionOn` and
  `Module.finBasis`.
