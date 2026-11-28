# Degree pieces of Jacquet functions

Module `Langlands.Representation.Shahidi.OpenCellPieces`, namespace
`Langlands.Shahidi.OpenCell`.

## Contents

- `detExponent hϖ m = ∑_i λ_i` for the Iwasawa exponent `λ` of `m` (the valuation of `det m`),
  invariant under integral right and upper unipotent left multiplication.
- `degreePiece hϖ e Φ (m₁, m₂) = [detExponent m₁ = e] Φ(m₁, m₂)`, Levi-invariant (resp.
  Levi-equivariant) when `Φ` is; `liftDegree`, `liftFunction_degreePiece`.
- `sphericalWhittaker_smul_eq`: for `ψ` of conductor `𝒪`,
  `W°(m; X a) = X^(detExponent m) W°(m; a)`; `fullΦ_smul`, `degreePiece_fullΦ_smul`,
  `jacquetFunction_degreePiece_smul` (same hypothesis): the degree-`e` pieces are homogeneous of
  degree `e` in the first parameters.
- `hasSum_integral_ite`: an integrable function is the sum of its restrictions to the level sets
  of an integer-valued function (each restriction assumed a.e. strongly measurable), at the
  level of integrals.
- `hasSum_jacquetFunction_degreePiece_torus`: for a Levi-invariant `Φ`, at a torus point where
  the Jacquet integrand is integrable, the Jacquet function is the sum of the Jacquet functions
  of its degree pieces; `hasSum_jacquetFunction_degreePiece`: the same at every point `g`, for a
  Levi-invariant `Φ` that is Levi-equivariant for the standard characters and whose Jacquet
  integrands are integrable at every torus point.
- `exists_hasSum_degreePiece`: for `ψ` of conductor `𝒪` there is `r₀ > 0` such that for
  `‖X‖ < r₀`, at every `g`,
  `∑_e X^e J_e(g) = J_(X a)(1) · W°(g; sectionParameter K (X a) c s)`, where `J_e` is the
  Jacquet function of the degree-`e` piece of the section with parameters `(a, c, s)`.

## Provenance

Derived from `Langlands.Representation.Shahidi.OpenCellShintani` and
`Langlands.Representation.Shahidi.OpenCellJacquetConvergence`.
