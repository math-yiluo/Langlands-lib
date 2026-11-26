# Translated Harish-Chandra components for points normalizing `U_J(𝔸)`

Module `Langlands.Global.AdelicLocalFinitenessComponentShifts` (namespace
`Langlands.Global.StandardParabolicFamily`). For a compatible standard parabolic family `𝓕`,
`Λ₀` is the image of `P₀(F)`, `D₀` its Library fundamental domain, `U_J` and `L_J` the unipotent
radical and Levi of the standard parabolic with index `J`, and `μ_W = 𝓕.weightedHaar W` the
measure `W · Haar` on `D₀`. The module `AdelicSplitComponentL2Translation` constructs the
operators "translate after the Harish-Chandra component" for images of points of the split
component `A_J`; this module constructs them for any point `b ∈ G(𝔸)` with

- `b x = x b` for every `x ∈ L_J(𝔸)`, and
- `b U_J(𝔸) b⁻¹ ⊆ U_J(𝔸)` and `b⁻¹ U_J(𝔸) b ⊆ U_J(𝔸)`.

## Results

- `setLIntegral_enorm_sq_mul_left_le`: for `J ⊆ Δ₀`, such a `b`, a measurable `f` and a
  measurable weight `W`, both left invariant under `Λ₀` and `U_J(𝔸)`, and `W(g) ≤ κ W(b g)`,
  `∫_{D₀} ‖f(b g)‖² W(g) dg ≤ κ c(b) ∫_{D₀} ‖f‖² W`, where `c(b)` is the Haar factor of
  conjugation by `b` on `U_J(𝔸)` (`mulEquivHaarChar (conjPoints F G b hb hb')`). Proof: bound
  `W(g)` by `κ W(b g)` and apply the translation formula `setLIntegral_mul_left_eq` (module
  `AdelicSplitComponentTranslation`) to `‖f‖² W`.
- `translatedComponent_of_point`: let `W` be a measurable weight, left invariant under `Λ₀` and
  under `U_K(𝔸)` for every `K ⊆ Δ₀` (this invariance for all `K` is a hypothesis of the theorem,
  stronger than the fixed-`J` invariance of the preceding bullet). Given contractions `T S` of
  `L²(μ_W)` computing the folded constant terms (as supplied by `exists_componentOperators`), a
  finset `P` with `J = (𝓕.finsetIndex P).1`, such a `b` and `W(g) ≤ κ W(b g)` with `κ < ∞`, there
  is a continuous linear operator `L` on `L²(μ_W)` with `‖L‖ ≤ (κ c(b))^{1/2} 2^{|P|}` and
  `L Fn = (g ↦ ∑_{S ⊆ P} (−1)^{|P ∖ S|} componentFoldCT S f (b g))` almost everywhere for every
  measurable representative `f` of `Fn`. The factor `2^{|P|}` counts the subsets in the
  alternating sum. The proof is that of `translatedComponent_of_operators` with the bound above:
  `InvariantTranslation.translateCLM` for the class of functions invariant under `Λ₀` and
  `U_J(𝔸)`.
- `IsLeviNormalizingPoint 𝓕 J b` is the conjunction of the three conditions above.
  `IsLeviNormalizingPoint.pow`: the powers `b^q`, `q ∈ ℕ`, satisfy them too; `weight_le_pow`:
  iterating the forward comparison gives `W(g) ≤ κ^q W(b^q g)` for `q ∈ ℕ`.
- `exists_translatedComponent_pow`: under the hypotheses of `translatedComponent_of_point` (in
  particular `W` measurable and left invariant under `Λ₀` and every `U_K(𝔸)`, `K ⊆ Δ₀`), a family
  `L q`, indexed by `q ∈ ℕ`, of such operators for the powers `b^q`.

Only non-negative powers are covered. The forward comparison `W(g) ≤ κ W(b g)` does not bound the
pullback by `b⁻¹` on weighted `L²` classes. For example, for `G_m` over `ℚ` with `H` the logarithm
of the idele norm, `W = 1_{H > 0}` and `H(b) = 1`, the forward comparison holds with `κ = 1`. But
the class of `1_{−1 < H < 0}` is zero in `L²(μ_W)`, while its pullback by `b⁻¹` is nonzero on the
band `0 < H < 1`, which has positive measure. A shift by `b⁻¹` needs its own forward comparison
`W(g) ≤ κ' W(b⁻¹ g)`, i.e. it is obtained by applying the results to the point `b⁻¹`.

## Provenance

Bernstein–Lapid, *On the meromorphic continuation of Eisenstein series*, J. Amer. Math. Soc.
37 (2024), 187–234 (literature id `bernstein-lapid-2024-meromorphic-continuation-eisenstein`).

- §7.5, p. 219: the proposition there translates on a relative Siegel domain by `a_α` and
  identifies the raw pullback `τ_α` with `δ_P(a_α)^{1/2} T_{a_α}`, where `T_a` is the twisted action
  `a·φ(g) = δ_P(a)^{−1/2} φ(a g)` of equation (6.2), p. 201. The operators of this module are raw
  left pullbacks `f ↦ f(b ·)` of the Harish-Chandra components; they enter the twisted equations
  `D_α(s)(T_{a_α})(f_P^𝔖) = 0` after multiplying by the scalar `δ_P(b)^{−1/2}`.
- §7.6, p. 219 (continuing on p. 220): the residual equations
  `D_α(s)(T_{a_α})(f_P^𝔖) = 0` of the system `Ξ^λ(s)` are polynomials in the translates by the
  powers of `a_α` of the Harish-Chandra components `f_P^𝔖`; these are the operators of this module
  for `b = a_α` and `q ∈ ℕ`.
- §7.7, pp. 220–221 (the case `A_G ≠ 1`): the central equations `D̃_i(s)^{ε_i}(T_{z_i}^{ε_i}) f^ε = 0`
  act within each orthant `ε ∈ {±1}^r` by the shift `T_{z_i}^{ε_i}`, with the reversed monic
  polynomial `D̃_i^−` in the negative direction. For these one applies the results separately in
  each orthant to the point `b = z_i^{ε_i}`, with the forward weight comparison
  `W(g) ≤ κ W(z_i^{ε_i} g)` for that point; by the remark above, the comparison for `z_i` does
  not give the shift by `z_i^{−1}`.
