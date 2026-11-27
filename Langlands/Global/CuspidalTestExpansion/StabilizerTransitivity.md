# Constant terms of stabilizer integrals along a larger unipotent group

Module `Langlands.Global.CuspidalTestExpansion.StabilizerTransitivity` (namespace
`Langlands.Global`).

Let `p : P → G`, `w ∈ G(𝔸)`, and `j : V → G` closed. Write `V(F)` for the rational points of
`range j` inside `V(𝔸)` and `Λ_V = V(F) ∩ wP(F)w⁻¹` (`stabilizerRationalSubgroup`).

## Declarations

- `stabilizerCosetSum p j w Φ x = ∑_{c ∈ Λ_V \ V(F)} Φ(w⁻¹ γ_c x)`, evaluated at the chosen
  representatives `γ_c`.
- `stabilizerCosetSum_mul_left`: for `Φ` left `P(F)`-invariant the sum is left invariant under
  `V(F)` (`EisensteinConstantTerm.tsum_out_mul_left`).
- `measurable_stabilizerCosetSum`: the sum is measurable for continuous `Φ`.
- `continuous_stabilizerCosetSum`: the sum is continuous if `Φ` is continuous and left
  invariant under `P(F)`, `w ∈ G(F)`, `0 < N`, and `‖Φ(γ_c g)‖ ≤ b c · H(g)^d` for every `g`
  and every coset `c ∈ P(F) \ G(F)` (with representative `γ_c`), where `b` is summable and
  nonnegative and `d ≥ 0`.
- `stabilizerIntegral_eq_subgroupConstantTerm`: let `V` be normal in `q : Q → G` (with
  `j = iV ≫ q`) with compact rational quotient `V(F) \ V(𝔸)`, and let `Φ` be continuous and
  left invariant under `P(F)`. If the stabilizer integrand at `z` is integrable, then
  `stabilizerIntegral p q iV w Φ z` is the constant term along `V` of the stabilizer coset sum at
  `z`.
- `subgroupConstantTerm_subgroupConstantTerm_of_le`: for closed `U ≤ V`, `U` normalized by `V`,
  both with compact rational quotients, and `f` continuous and left invariant under `V(F)`, the
  constant term along `V` of the constant term along `U` of `f` is the constant term along `V`
  of `f`.
- `stabilizerCosetSum_eq_of_le`: let `Φ` be left invariant under `P(F)` (`hΦP`). If
  `range jQ ≤ range jJ` and every rational point of `U_J` is a point of `Λ_{U_J}` times a
  rational point of `U_Q`, the stabilizer coset sums of `Φ` along `U_Q` and along `U_J`
  coincide. The `P(F)`-invariance is what makes the summands `Φ(w⁻¹ γ x)` independent of the
  representative `γ` of a coset of `Λ_{U_J}`.
- `subgroupConstantTerm_stabilizerIntegral_of_le`: assume `U_Q ≤ U_J`, each normal in its
  parabolic (`hNQ`, `hNJ`) and with compact rational quotient, `U_Q` normalized by `U_J`,
  `w ∈ G(F)`, the factorization `U_J(F) ⊆ Λ_{U_J} U_Q(F)`, `0 < N`, `Φ` continuous and left
  `P(F)`-invariant with a majorant as in `continuous_stabilizerCosetSum`, the stabilizer
  integrand along `U_Q` integrable at every argument and the one along `U_J` integrable at `y`.
  Then the constant term along `U_J` of the stabilizer integral along `U_Q`, at `y`, is the
  stabilizer integral along `U_J` at `y`.

## Proofs

Continuity: the map `c ↦ [w⁻¹ γ_c] ∈ P(F) \ G(F)` is injective, since `w⁻¹ γ_{c'} γ_c⁻¹ w ∈ P(F)`
forces `γ_{c'} γ_c⁻¹ ∈ Λ_V`. Hence `‖Φ(w⁻¹ γ_c x)‖ ≤ b([w⁻¹ γ_c]) H(x)^d` with a summable
majorant (`Summable.comp_injective`). On the open set `H < H(x₀) + 1` the series converges
uniformly (`continuousOn_tsum`); the adelic height is continuous (`continuous_adelicHeight`).

`stabilizerIntegral_eq_subgroupConstantTerm`: `EisensteinConstantTerm.unfold_conj` (with the
rational point `1` of `Q` and the representatives of `Λ_V \ V(F)`) rewrites the stabilizer
integral as the integral over a fundamental domain of `V(F)` in `V(𝔸)` of the coset sum; the
finiteness it requires is the integrability hypothesis. The normalized quotient measure is the
push-forward of the normalized Haar measure restricted to that domain
(`normalizedRationalQuotientHaarMeasure_eq_quotientMeasure`), and
`RankinSelbergGlobal.Unfolding.integral_out_eq` identifies the two integrals, using the
`V(F)`-invariance of the coset sum.

`subgroupConstantTerm_subgroupConstantTerm_of_le` follows the proof of the Library's
`AdelicSubgroupPoints.integral_normalizedConstantTerm_eq_of_isNormalizedBy`, with the
invariance of `f` required only under `V(F)`: the function `n ↦ f(n g)` descends to the compact
quotient `V(F) \ V(𝔸)` (`LeftCosetSpace.lift`), and `LeftCosetSpace.integral_compactSubgroupAverage`
(averaging over the compact quotient `U(F) \ U(𝔸)` preserves the invariant probability integral)
gives the identity; conjugation by rational points of `V` preserves the probability measure of
`U(F) \ U(𝔸)` (`measurePreserving_rationalQuotientAutomorphism`).

`stabilizerCosetSum_eq_of_le` is `CosetTransfer.tsum_cosetEquiv` for the inclusion
`U_Q(F) → U_J(𝔸)`: the preimage of `Λ_{U_J}` is `Λ_{U_Q}` (both are defined by
`w⁻¹ x w ∈ P(F)`), and the factorization hypothesis gives surjectivity on cosets. The function
`a ↦ Φ(w⁻¹ a x)` is left invariant under `Λ_{U_J}`, because for `a ∈ Λ_{U_J}` one has
`w⁻¹ a y x = (w⁻¹ a w)(w⁻¹ y x)` with `w⁻¹ a w ∈ P(F)` and `Φ` is left `P(F)`-invariant.

`subgroupConstantTerm_stabilizerIntegral_of_le`: write both stabilizer integrals as constant
terms of the same coset sum `S` (the two previous items), and apply the transitivity to `S`,
which is continuous and, being the coset sum of `U_J`, left invariant under `U_J(F)`.
