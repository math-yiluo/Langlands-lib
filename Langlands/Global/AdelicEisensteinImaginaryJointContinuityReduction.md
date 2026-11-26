# Joint continuity on the imaginary axis from the root-hyperplane form

Module `Langlands.Global.AdelicEisensteinImaginaryJointContinuityReduction`, namespace
`Langlands.Global`.

The module states

```
def EisensteinImaginaryJointContinuityReductionStatement : Prop :=
  EisensteinJointRootHyperplaneStatement.{0} → EisensteinImaginaryJointContinuityStatement
```

and proves it (`eisensteinImaginaryJointContinuityReduction`). Combined with
`wavePacketSiegelDecay_of_reduction`, it gives

```
theorem wavePacketSiegelDecay_of_jointRootHyperplane
    (hJ : EisensteinJointRootHyperplaneStatement.{0})
    (hchamber : WavePacketChamberDecayStatement) : WavePacketSiegelDecayStatement
```

`EisensteinJointRootHyperplaneStatement` (`Langlands/Global/AdelicEisensteinJointRootHyperplaneStatement.lean`)
and `WavePacketChamberDecayStatement` (`Langlands/Global/AdelicWavePacketSiegelDecayReduction.lean`)
are hypotheses here. Neither is proved in this module.

## The statements used

- `EisensteinJointRootHyperplaneStatement` (Bernstein–Lapid 2024, Theorem 2.3 (1) and (6) with
  the Corollary in §8.6). For a pointwise continuation `(EP, DP)` of the Eisenstein series of an
  automorphic form `φ` on `P(F) U(𝔸) \ G(𝔸)`, near every point `s₀` of a complex linear chart
  `e` there are:
  - a finite set `S` of roots `β`, each with nonzero real root form;
  - an exponent `k`;
  - an open `W ∋ s₀`;
  - a function `h(s, g)`, continuous on `W × G(𝔸)`, such that
    `h(s, g) = (∏_{β ∈ S} B(e s - e s₀, β))^k · EP(e s)(g)` whenever `e s ∈ DP`.

  Here `B(·, β)` is `ParabolicRootPresentation.rootFunctional`, the complex-linear extension of
  the real root form `realRootFunctional`.
- Lapid 2011 (registered as `lapid-2011-asymptotic-inner-product-truncated-eisenstein`),
  Proposition 6 and its proof, printed pp.329–330 (PDF pp.338–339). Lapid argues by
  contradiction against a pole of `E_P(·, φ₀, λ)` along a root hyperplane through
  `λ₀ ∈ i𝔞_P^*`. He uses the cleared function `E*(x, λ) = l(λ)^k E_P(x, φ₀, λ)` and compares
  `E*(x, λ)` with `E*(x₀, λ)` for `x` in a compact neighbourhood of `x₀`, uniformly for
  `‖λ - λ₀‖ < r`. The argument implemented here is different: it starts from the scalar
  holomorphy of each `λ ↦ E(λ)(g)` on the supplied domain `D` and applies the Cauchy formula
  along a direction transverse to the root hyperplanes, so that only the continuity of the
  cleared function is used.
- `EisensteinImaginaryJointContinuityStatement`: for a continuation `(E, D)` of the Eisenstein
  series of `φ ∈ A^2_P` with `D ⊇ i𝔞_P^*`, the map `(x, g) ↦ E(i e(x))(g)` is continuous on
  `ℝⁿ × G(𝔸)` for all real linear coordinates `e`.

## The proof

### Analytic lemmas

- `continuousOn_intervalIntegral_of_continuousOn`: if `f(x, θ)` is continuous on `s × ℝ`, then
  `x ↦ ∫_a^b f(x, θ) dθ` is continuous on `s`. The proof uses uniform convergence on the compact
  interval (`IsCompact.mem_uniformity_of_prod`) and the bound
  `intervalIntegral.norm_integral_le_of_norm_le_const`. The interval-integral lemma applies to
  an arbitrary topological parameter space.
- `continuousAt_of_rootHyperplane_cleared` is the core. Its hypotheses are the following.
  - `E'(s)(g)` is holomorphic in `s` on an open `O ∋ s₀` for every `g`.
  - `L_β`, `β ∈ S`, are finitely many complex linear forms on `ℂ^m`, each not identically zero,
    and `k` is an exponent.
  - `h` is continuous on `W × X` for an open `W ∋ s₀`, and
    `h(s, g) = (∏_β L_β(s - s₀))^k · E'(s)(g)` for every `s ∈ W ∩ O` and every `g ∈ X`. In the
    application `O` is the preimage of `D` under the complex coordinates.

  The conclusion is that `(s, g) ↦ E'(s)(g)` is continuous at `(s₀, g₀)`. The proof has five
  steps.
  1. A direction `v` with `L_β(v) ≠ 0` for every `β`
     (`Module.Dual.exists_forall_ne_zero_of_forall_exists`: a vector space over an infinite
     field is not a finite union of proper subspaces).
  2. Radii. Take `δ > 0` with `ball(s₀, δ) ⊆ W ∩ O`, put `r = δ / (2(‖v‖ + 1))`, and let `U`
     be the set of `s ∈ ball(s₀, δ/2)` with `‖L_β(s - s₀)‖ < r ‖L_β(v)‖` for every `β`. `U` is
     an open neighbourhood of `s₀`. For `s ∈ U` and `|ζ| ≤ r`, the point `s + ζ v` lies in
     `ball(s₀, δ) ⊆ W ∩ O`.
  3. On the circle `|ζ| = r` no root form vanishes:
     `L_β(s + ζ v - s₀) = L_β(s - s₀) + ζ L_β(v)`, and the second term has the larger norm.
     There `E'(s + ζ v)(g) = h(s + ζ v, g) / (∏_β L_β(s + ζ v - s₀))^k`.
  4. Cauchy's formula (`Complex.two_pi_I_inv_smul_circleIntegral_sub_inv_smul_of_differentiable_on_off_countable`,
     with the empty exceptional set) gives, for `s ∈ U`,
     `E'(s)(g) = (2πi)⁻¹ ∮_{|ζ| = r} ζ⁻¹ E'(s + ζ v)(g) dζ`. By step 3 the integrand on the
     circle is `ζ⁻¹ · h / (∏ L_β)^k`, which is jointly continuous in `(s, g, ζ)` on
     `U × X × {|ζ| = r}`.
  5. Writing the circle integral as an interval integral over `[0, 2π]`, the first lemma shows
     that the right side is continuous on `U × X`. It equals `E'` there, and `U × X` is a
     neighbourhood of `(s₀, g₀)`.
- `ParabolicRootPresentation.exists_rootFunctional_ne_zero`: if `realRootFunctional β ≠ 0`, then
  `rootFunctional β (1 ⊗ χ) ≠ 0` for some rational character `χ`. A real-linear form on
  `ℝ ⊗ X^*(P)` vanishing on all `1 ⊗ χ` vanishes on all `x ⊗ χ = x • (1 ⊗ χ)`, hence is zero
  (`TensorProduct.AlgebraTensorModule.ext`). Moreover `rootFunctional β (1 ⊗ χ)` is the real
  number `realRootFunctional β (1 ⊗ χ)` (`rootFunctional_tmul`).

### `eisensteinImaginaryJointContinuityReduction`

Fix the data and a continuation `(E, D)` with `D ⊇ i𝔞_P^*`. Choose complex coordinates
`e_ℂ : ℂ^m ≃ X^*(P) ⊗ ℂ` from a basis.

- At every `s₀` with `e_ℂ s₀ ∈ D`, apply `EisensteinJointRootHyperplaneStatement` to `(E, D)`.
  This is allowed because `A^2_P` forms are automorphic forms on `P(F) U(𝔸) \ G(𝔸)`, the first
  clause of `IsSquareIntegrableInducedForm`. Then apply the core lemma with:
  - `E'(s)(g) = E(e_ℂ s)(g)`, holomorphic on the open set `e_ℂ⁻¹ D`
    (`IsMeromorphicInCoordinatesOn`, `differentiableOn_of_isHolomorphicOn`);
  - `L_β = rootFunctional β ∘ e_ℂ`, nonzero by the previous lemma.

  This gives joint continuity of `(s, g) ↦ E(e_ℂ s)(g)` at `(s₀, g₀)` for every `g₀`.
- The map `x ↦ e_ℂ⁻¹(imaginaryParameter(e x))` is real-linear on `ℝⁿ`, hence continuous
  (`LinearMap.continuous_of_finiteDimensional`). Its values are points `s₀` with
  `e_ℂ s₀ ∈ i𝔞_P^* ⊆ D`. Composing gives continuity of `(x, g) ↦ E(i e(x))(g)` at every point.

The proofs use only the standard axioms (`propext`, `Classical.choice`, `Quot.sound`).

## What is not proved here

`EisensteinJointRootHyperplaneStatement` and `WavePacketChamberDecayStatement`.
