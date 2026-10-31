# Inverse-transpose substitution in transformed matrix integrals

Module `Langlands.Representation.GodementJacquet.InverseTransposeMatrixIntegral`.
Author: Worker 1117.

This module rewrites the transformed Godement–Jacquet matrix integral
`Z(Φ, s, f^ι)` as an integral of `f` itself. Here `f^ι = coefficientIota f`
is `g ↦ f (ι g)`, where `ι g = (g⁻¹)ᵀ` is `GeneralLinear.inverseTranspose`.
The rewriting substitutes `g ↦ ι g` in the group integral. It is a helper for
the transformed side of the two-block functional equation (Godement–Jacquet,
*Zeta Functions of Simple Algebras* (1972), proof of Theorem 3.4, printed
36–45). Godement–Jacquet state the transformed side with the pair `(Φ̂, f̌)`,
`f̌(g) = f(g⁻¹)`, a coefficient of the contragredient representation. The
project follows Jacquet–Piatetski-Shapiro–Shalika, *Automorphic Forms on
GL(3) I* (1979), (0.4.3) on printed 174, and uses `coefficientIota` of the
representation's own coefficients (see the Markdown of
`TwoBlockMatrixFunctionalEquationInductionStatement`, "Convention adaptation"). After this substitution the transformed
integral can be computed with the same parabolic coordinates and compact
coefficient data as the untransformed one, so no comparison with a
contragredient representation is needed.

## Definitions

- `inverseTransposeSubstitutedIntegrand abv Φ s f g` is
  `Φ (ι g) * f g * determinantWeight abv g (-s)`. It is defined for any field
  `F` with a topology, any absolute value `abv`, any matrix test function `Φ`
  on `(n+1) × (n+1)` matrices, any complex `s` and any function `f` on
  `GL_(n+1)(F)`. Here `determinantWeight abv g s = |det g|^s`, and `Φ (ι g)`
  means `Φ` applied to the underlying matrix of `ι g`.
- `inverseTransposeMeasurableEquiv hι` is the involution `ι` as a measurable
  equivalence of `GL_(n+1)(F)`, given a proof `hι` that `ι` is measurable.
  Since `ι` is its own inverse, `hι` serves for both directions.

## Results and proofs

- `matrixIntegrand_coefficientIota_inverseTranspose`: for every `g`,
  `matrixIntegrand abv Φ s (coefficientIota f) (ι g) =
  inverseTransposeSubstitutedIntegrand abv Φ s f g`. Proof: unfold both sides;
  `ι (ι g) = g` (`GeneralLinear.inverseTranspose_involutive`) and
  `|det (ι g)|^s = |det g|^(-s)` (`determinantWeight_inverseTranspose`).
- `matrixConverges_coefficientIota_iff`: let `μ` be any measure on
  `GL_(n+1)(F)` such that `ι` is measure preserving from `μ` to `μ`. Then
  `MatrixConverges abv μ Φ s (coefficientIota f)` holds if and only if
  `inverseTransposeSubstitutedIntegrand abv Φ s f` is `μ`-integrable. Proof:
  `MeasurePreserving.integrable_comp_emb` along the measurable equivalence `ι`,
  and the previous pointwise identity.
- `matrixIntegral_coefficientIota`: under the same hypothesis on `μ`,
  `matrixIntegral abv μ Φ s (coefficientIota f) =
  ∫ g, inverseTransposeSubstitutedIntegrand abv Φ s f g ∂μ`. Proof:
  `MeasurePreserving.integral_comp` along the same measurable embedding. No
  integrability hypothesis is needed.
- `Padic.generalLinearHaar_measurePreserving_inverseTranspose`: for a p-adic
  field `F` with its canonical topological data and the Borel measurable
  structure on `GL_(n+1)(F)`, the inverse transpose preserves the canonical
  normalized Haar measure `generalLinearHaar F.Carrier n` on `GL_(n+1)(F)`.
  This is the second component of the published `generalLinearHaarSymmetries`.

The last result supplies the hypothesis on `μ` for the group measure used in
`Padic.NormalizedMatrixFunctionalEquationData`.

## Scope

The identities are pointwise or measure-theoretic and involve no
representation theory: `f` is an arbitrary complex function on the group.
Measurability of `ι` is taken from the measure-preservation hypothesis. Only
the canonical p-adic case is given for the Haar measure.
