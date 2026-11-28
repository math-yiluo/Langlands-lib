# The shell identities for the `(1, n)` parabolic

Module `Langlands.Representation.Shahidi.OpenCellBaseShell`, namespace
`Langlands.Shahidi.OpenCell.Base`.

## Contents

Throughout, the results other than the definitions assume that `ψ` has conductor `𝒪` (additive
conductor `0`).

- `fullΦ ψ hϖ a c s (m₁, m₂) = δ_P(m₁, m₂)^(1/2 + s/N) W°(m₁; a) W°(m₂; c)`: the Levi function
  of the target statement, with `isLeviInvariant_fullΦ`; `eq_liftFunction_of_isOpenCellSection`:
  a function with the target transformation law is its lift; `openCellSummand_eq_lower`.
- `sphericalWhittaker_rankOne`: on `GL_1`, `W°(u ϖ^λ; a) = a^λ`;
  `isWhittakerType_sphericalWhittaker`: `W°(·; c)` is of Whittaker type;
  `summable_baseIntegrand` (no conductor hypothesis; `Ψ` right `GL(𝒪)`-invariant): the
  rank-one integrand is absolutely summable over the classes.
- `liftFunction_fullΦ_eq`: on the depth-`D` shell the lift of `fullΦ` (first block of rank one) is
  `baseCoef t D a s` times the lift of `shellΦ D W°(·; c)`; `shellCoefficient_rankOne`:
  `shellCoefficient (pairParameter q a c s) D = (-a q^(-(1+s)))^D e_D(c⁻¹)`.
- `baseCoef_mul_baseValue`: `baseCoef · baseValue(D, W°(·; c)) = shellCoefficient
  (pairParameter q a c s) D`. For `D ≤ t + 1` this uses the Schur evaluation of
  `Langlands.Representation.Shahidi.OpenCellBaseSchur` (valid only in that range) and the
  constant identity of `Langlands.Representation.Shahidi.OpenCellBaseCoef`; for `D > t + 1` both
  sides vanish (the base value by its support, the coefficient since there are no `D`-element
  subsets of `t + 1` indices).
- `shellIdentity_rankOne`: for `ψ` of conductor `𝒪` and a function with the target
  transformation law, the shell identities hold when the first block has rank one.

## Provenance

Derived from `integral_baseIntegrand` (`Langlands.Representation.Shahidi.OpenCellBaseInduction`)
and the class-sum formula of `Langlands.Representation.Shahidi.OpenCellHaar`.
