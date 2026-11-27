# Smooth slices of intertwining integrals from uniform growth: proof

Module `Langlands.Global.AdelicIntertwiningSmoothSlicesReduction`. The theorem

```lean
theorem Langlands.Global.intertwiningSmoothSlicesReduction :
    IntertwiningSmoothSlicesReductionStatement.{u}
```

proves the published implication
`AutomorphicFunctionUniformGrowthStatement.{u} → IntertwiningSmoothSlicesStatement.{u}`. It is the
term `fun h2 => intertwiningSmoothSlices_of_uniformGrowth h2`. The premise is not proved here. Lean reports the axioms `propext`, `Classical.choice` and `Quot.sound`.

## The proof of `intertwiningSmoothSlices_of_uniformGrowth`

Fix the data of `IntertwiningSmoothSlicesStatement`, a finite adelic point `b`, and write `W` for
the adelic point of `w`, `j = iV ≫ q`, `Λ = V(F) ∩ W U(𝔸) W⁻¹` and `H` for the adelic height of
`rho`.

**Size zero.** If `N = 0`, the closed immersion `rho` into `GL_0` makes the infinite adelic points a
subsingleton (`MatrixRepresentation.pointMatrix_injective`), so every slice is constant and smooth;
`R₀ = 0` serves.

**Inputs.** For `N > 0`, the Library's `adelicSmoothIwasawaHeight` gives smooth height pairings
for `hK` and for `hK'`, since `K` is maximal compact and `p`, `q` are closed immersions. Maximality of `K` gives that `K`
contains the infinite components of its elements (`IsMaximalCompactSubgroup.mem_iff`) and that its
infinite part is maximal compact. The premise, with `Γ = U(𝔸) M(F)`, and
`exists_hasUniformSliceGrowth` give `e ≥ 0` with `HasUniformSliceGrowth hsmooth Γ H e φ`.

**One threshold.** Let `E(y) = inf_{γ ∈ Γ} H(γ y) ^ e` (the private `leftEnvelope`). It is
nonnegative, at most `H(y) ^ e`, left `Γ`-invariant, hence of moderate growth, and every
`Γ`-invariant `ψ` with `‖ψ‖ ≤ C H ^ e` satisfies `‖ψ‖ ≤ C E` (`norm_le_mul_leftEnvelope`). The
Library's `eisensteinGlobalMajorant`, applied to `E`, gives the threshold `R₀`. For an `R₀`-regular
`λ` it gives a summable Eisenstein majorant, and `exists_integrable_unfolding_majorant` (with the
fibre lemma `mul_inv_mem_intertwiningRationalSubgroup` and the rational Levi
`r.isCompatible.levi`) gives an integrable `B` on `Λ \ V(𝔸)` and `dE ≥ 0` with
`‖E_λ(W⁻¹ v g)‖ ≤ B(v) H(g) ^ dE`.

**The family of integrands.** For a list `ws` of directions let `ψ ws` be the iterated twisted
derivative `IsIwasawaCompact.parameterDirectionalSection λ` of `φ` along `ws`. By
`hasUniformSliceGrowth_parameterDirectionalSection` (with `parabolicQuotientSubgroup_le_range`),
every `ψ ws` has uniform slice growth with the same `e`. Put
`f ws x a = (ψ ws)_λ(W⁻¹ v_x (a, b))`, where `v_x` is the chosen representative of `x`. Then:

- each `f ws x` is smooth (`contMDiff_parameterTwist_slice` and left translation);
- `D_X (f ws x) = f (ws ++ [X]) x`, by left translation and
  `IsIwasawaCompact.parameterTwist_directionalSection`;
- `f ws · a` is almost everywhere strongly measurable: for `ws = []` the integrand is continuous on
  the quotient (`continuous_intertwiningIntegrand`), and derivatives preserve measurability
  (`aestronglyMeasurable_groupDirectionalValue`);
- locally uniform domination: `‖f ws x a‖ ≤ C_ws E(y) |m_P(y)^λ| ≤ C_ws B(x) H((a, b)) ^ dE` with
  `y = W⁻¹ v_x (a, b)`, and `H((a, b))` is bounded near any `a₀` by continuity.

`contMDiff_integral_of_dominated_invariantDerivatives` then shows that
`a ↦ ∫ f [] x a dx = intertwiningIntegral φ λ (a, b)` is smooth. The operator is the product with
`a ↦ m_Q((a, b))^{-wλ} = exp ⟨-wλ, H_Q(a, b)⟩`, smooth by `adelicSmoothIwasawaHeight` for `hK'`, and
`isPlotSmooth_iff_contMDiff` gives membership in `InfinitePlotSmoothFunctions`.

## Provenance

Mœglin–Waldspurger, *Spectral decomposition and Eisenstein series* (1995), II.1.6, Proposition (i),
printed pp. 87–88, gives the automorphy of the regular intertwining integral and its absolute
convergence, uniformly on compact sets; the proof on p. 88 bounds the absolute integral by an
Eisenstein sum integrated over the compact quotient `U'(k) \ U'(𝔸)` and applies II.1.5. The proof
here establishes the smoothness in the infinite variable by a different, formal route: the family of
twisted sections closed under invariant derivatives (`parameterDirectionalSection`), one envelope
bounding all of its members, the Library's Eisenstein and unfolding majorant for that envelope, and
differentiation under the integral sign on the Lie group of infinite points. The common growth
exponent is uniformly moderate growth in the sense of I.2.3 (printed p. 25), which Mœglin–Waldspurger
derive for automorphic forms on `U(𝔸) M(k) \ G` at the end of I.2.17 (printed pp. 38–39) from
I.2.5, Lemma (a) (printed p. 27); here it is the premise `AutomorphicFunctionUniformGrowthStatement`.
