# Product Levi functions, rank-one shells and the graded Shintani identity

Module `Langlands.Representation.Shahidi.OpenCellGraded`, namespace
`Langlands.Shahidi.OpenCell`.

## Contents

- `prodΦ s Ψ₁ Ψ₂ (m₁, m₂) = δ_P(m₁, m₂)^(1/2 + s/N) Ψ₁(m₁) Ψ₂(m₂)`; `fullΦ_eq_prodΦ` (by
  definition) and `isLeviInvariant_prodΦ` (for `Ψ₁`, `Ψ₂` right invariant under the integral
  groups).
- `liftFunction_prodΦ_eq` (for `ψ` of conductor `𝒪` and `Ψ` right `GL_(t+1)(𝒪)`-invariant),
  `jacquetFunction_degreePiece_prodΦ_rankOne`: for `ψ` of conductor `𝒪`, a first block of rank
  one and any Whittaker-type `Ψ`, `J[(prodΦ s W°(·; a) Ψ)_D](1) = baseCoef t D a s ·
  baseValue ϖ t D Ψ`, by `integral_baseIntegrand`.
- `sectionParameter_zero`: at `s = 0` the Satake parameter is `Fin.append a c`;
  `pairParameter_smul`: `pairParameter q (X a) c s = X · pairParameter q a c s`.
- `CoreAt ψ hϖ r t`: the shell identities at `s = 0` for the ranks `(r, t)`, as identities
  `J[(fullΦ a c 0)_D](1) = shellCoefficient (pairParameter q a c 0) D` for all `a`, `c`, `D`.
- `jacquetFunction_one_eq_prod_of_core`: for `ψ` of conductor `𝒪` and under `CoreAt r t`, there
  is `r₀ > 0` such that for `‖X‖ < r₀`,
  `J[fullΦ (X a) c 0](1) = ∏_x (1 - X pairParameter q a c 0 x)`.
- `exists_hasSum_degreePiece_of_core`: for `ψ` of conductor `𝒪` and under `CoreAt r t`, there is
  `r₀ > 0` such that for `‖X‖ < r₀` and every `g`,
  `∑_e X^e J_e(g) = ∏_x (1 - X pairParameter q a c 0 x) · W°(g; Fin.append (X a) c)`.

## Provenance

Derived from `Langlands.Representation.Shahidi.OpenCellPieces`,
`Langlands.Representation.Shahidi.OpenCellShellSum` and
`Langlands.Representation.Shahidi.OpenCellBaseInduction`.
