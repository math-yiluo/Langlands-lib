# Derivatives at the identity of archimedean logarithms and normalizing factors

Module `Langlands.Global.InfiniteAdelicCharacterDerivative`, namespace
`Langlands.Global.InfiniteAdelicGroupPoints`. The setting and the notation `D_X`
(`regularDerivative`) are those of `InfiniteAdelicTangentKernel`; `mult(v)` is 1 at real and 2
at complex places.

## Declarations

- `hasFDerivAt_log_norm_sq_one`: in an `RCLike` field, `z ↦ log ‖z‖²` has real derivative
  `2 Re` at `1`. Here `‖z‖² = (Re z)² + (Im z)²`, and the chain rule is applied to `log`.
- `placeValue_one`: the value at the identity is `identityValue`.
- `mfderiv_archimedeanLogRegular_one`: if a regular function `s` takes the value `1` at the
  identity, the derivative at the identity along `X` of the published
  `archimedeanLogRegular F G s = log ∏_v ‖s_v‖^{mult(v)}` is `Σ_v mult(v) · Re (D_X s)_v`.
  On the open neighbourhood of the identity where all `s_v` are nonzero, the function equals
  `Σ_v (mult(v)/2) · log ‖s_v‖²`. The sum rule and `hasFDerivAt_log_norm_sq_one` give the
  derivative.
- `identityValue_characterRegularFunction`: the regular function of a rational character
  (`characterRegularFunction`) takes the value `1` at the identity.
- `mfderiv_parameterPower_tmul_one`: for a morphism `j : G ⟶ H`, `c ∈ ℂ` and a rational
  character `ψ` of `H`, the derivative at the identity along `X` of
  `m ↦ j(m)^{c ⊗ ψ}` (`parameterPower` of `map j (ofInfinite m)`) is
  `c · Σ_v mult(v) · Re (D_X (ψ ∘ j))_v`. The function is
  `m ↦ exp(c · archimedeanLogRegular F G (ψ ∘ j) m)`, by the published `characterLog_map` and
  `characterLog_apply_ofInfinite`. The logarithm vanishes at the identity, and the chain rule
  applies.
- `mfderiv_halfModulus_one`: for a parabolic-type group `P` (affine, locally of finite type)
  and `j : G ⟶ P`, the derivative at the identity along `X` of the normalizing factor
  `m ↦ j(m)^{-ρ_P}` is `-1/2 · Σ_v mult(v) · Re (D_X (det Ad_P ∘ j))_v`. Here
  `-halfModulusParameter F P = (-1/2) ⊗ det(Ad | Lie P)`.

## Provenance

Internal calculus on the Library's archimedean manifolds. The factor `m ↦ j(m)^{-ρ_P}` is the
normalization `δ_P(j(m))^{-1/2}` of Mœglin–Waldspurger I.2.17 and Bernstein–Lapid (6.5), as
used in `LeviRestrictionCenterTransferStatement`.
