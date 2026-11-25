# Matching of the two Hecke families at unramified places

Supporting module for the proof of `AssociatedGammaStatement` (module
`Langlands.Automorphic.AssociatedGammaOutsideMatch`, namespace
`Langlands.ClassFieldTheory.Global.RelativeWeilGroup`). The two-twist engine used for
`AssociatedGammaStatement` (Henniart 2000, Théorème 2.3) needs the automorphic and arithmetic
local L-factors to agree outside a finite set (`MatchesOutside`). This module proves the
agreement at a place where everything is unramified and weak association applies. Internal
deduction from Library results and the earlier supporting modules of this proof.

## Results

- `eval_inv_algebraMap_total`: `RatFunc.eval x (1/P) = (P(x))⁻¹` for every `x`, including
  zeros of `P` (both sides `0` there). This makes the agreement hold for every `s`, so no
  uniform half-plane is needed.
- `map_product_map`, `pairEulerPolynomial_scale`, `eigenvalues_eulerPolynomial_eq`: multiset
  bookkeeping that writes the pair Euler polynomial of a scaled Satake multiset, and the
  Euler polynomial of a Satake multiset, as products over complex numbers.
- `arithmeticPairLFactor_eq_pairEulerPolynomial`: for presentations `Q`, `Q'` and relative
  Weil representations `S₀`, `S₀'` that are unramified at `z` and match the Euler polynomials
  of `Q`, `Q'` there (`IsUnramifiedMatchAt`), and a Hecke character `χ` unramified at `z`,
  the arithmetic pair L-factor of `((χ ∘ τ_F) ⊗ S₀, S₀')` along a local map equals
  `1 / pairEulerPolynomial(Satake(Q ⊗ χ), Satake(Q'))`. The Satake parameters of the
  twisted presentation are scaled by `χ_z(ϖ)` (published `heckeDeterminantTwist_spectralSystem`),
  matching the `arithmeticPairLFactor_twist_of_unramified`.
- `lFactor_eq_of_unramified`: for the automorphic family of an `AutomorphicTwistSetup` and
  the arithmetic family of an `ArithmeticTwistSetup`, at a place outside the unramified set
  of the twisted factor choice and the exceptional sets, where `χ` is unramified and `S`, `S'`
  match the Satake parameters of `P`, `P'`, the two local L-factors agree at every `s`.
- `localPairClass_twist_dual_eq`: the local class of the dual of `(η ⊗ S₀)` is that of
  `η⁻¹ ⊗ S₀^∨` (identity map; `(c f)^* = c f^*` and `η((ι g)⁻¹) = η⁻¹(ι g)`).
- `HeckeCharacter.isUnramifiedAt_inv`: `χ⁻¹` is unramified where `χ` is.
- `dualLFactor_eq_of_unramified`: the dual local L-factors of the two families agree at
  every `s` at a place outside the unramified set of the twisted factor choice and the
  exceptional sets of the contragredient presentations `Pd`, `Pd ⊗ χ⁻¹`, `Pd'`, where `χ` is
  unramified and `S^∨`, `S'^∨` match the Satake parameters of `Pd`, `Pd'`. The arithmetic
  dual class is rewritten as the twist of `S^∨` by `χ⁻¹ ∘ τ_F`, and
  `arithmeticPairLFactor_eq_pairEulerPolynomial` is applied to `Pd`, `Pd'`, `S^∨`, `S'^∨`, `χ⁻¹`.
