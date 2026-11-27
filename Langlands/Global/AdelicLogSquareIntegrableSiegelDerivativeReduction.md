# Reduction of the logarithmic Siegel bounds to a local `L²` bound and a Siegel count

Module `Langlands.Global.AdelicLogSquareIntegrableSiegelDerivativeReduction`, namespace
`Langlands.Global`.

| Declaration | Kind |
| --- | --- |
| `exists_adelicLogHeight_mul_le` | theorem |
| `logSquareIntegrableSiegelDerivativeBounds_of_reduction` | theorem |

The module proves that two propositions imply
`LogSquareIntegrableSiegelDerivativeBoundsStatement` (module
`Langlands.Global.AdelicLogSquareIntegrableSiegelDerivativeBounds`, Delorme 2023,
Proposition 3.5, (ii) implies (i)):

```
theorem logSquareIntegrableSiegelDerivativeBounds_of_reduction
    (hA : AdelicLocalL2DerivativeBoundStatement)
    (hB : SiegelRationalConjugateCountingStatement) :
    LogSquareIntegrableSiegelDerivativeBoundsStatement
```

- `AdelicLocalL2DerivativeBoundStatement` (module
  `Langlands.Global.AdelicLocalL2DerivativeBoundStatement`): for a left `G(F)`-invariant,
  smooth, `K_∞`-finite and `𝔷`-finite `Φ` and a word `D`, there are a compact `S ⊆ G(𝔸)` and
  `C` with `‖D Φ(g)‖² ≤ C ∫_S ‖Φ(g s)‖² ds` for all `g`. It is a consequence of
  Harish-Chandra's smooth reproducing kernel, and the module
  `Langlands.Global.AdelicLocalL2DerivativeBoundProof` proves it
  (`adelicLocalL2DerivativeBound`).
- `SiegelRationalConjugateCountingStatement` (module
  `Langlands.Global.AdelicSiegelRationalConjugateCountingStatement`): for a compact `E`, the set
  `G(F) ∩ x E x⁻¹` is finite with at most `B · δ_{P₀}(a)` points at every Siegel point `x` with
  torus coordinate `a`.

This module does not prove either proposition, so the target statement remains conditional on
them here. The exponent produced for the target is the exponent `m` of the weighted `L²`
hypothesis of `IsLogSquareIntegrableAutomorphicForm`, the same for every word `D`.

## The height lemma

`exists_adelicLogHeight_mul_le rho hrho hS`: for a closed matrix embedding `rho` and a compact
`S ⊆ G(𝔸)` there is `L ≥ 1` with `σ(x s) ≤ L σ(x)` for all `x ∈ G(𝔸)` and `s ∈ S`, where
`σ = adelicLogHeight F G rho = 1 + log max(1, ‖·‖_ρ)`.

*Proof.* If `rho` has size `0`, the closed embedding `RepresentationGrowth.adelicMatrix` into
`GL_0` makes `G(𝔸)` a subsingleton, so `x s = x` and `L = 1`. Otherwise the height
`RepresentationGrowth.adelicHeight` is continuous (`continuous_adelicHeight`), so it is bounded on
`S` by some `M' ≥ 1`. The height is submultiplicative (`adelicHeight_mul_le`) and is the source
norm times the positive constant `N^{∑_v m_v}` (`adelicHeight_eq_scalar_mul_sourceNorm`), so
`‖x s‖_ρ ≤ ‖x‖_ρ M'` and `max(1, ‖x s‖_ρ) ≤ max(1, ‖x‖_ρ) M'`. Taking logarithms,
`σ(x s) ≤ σ(x) + log M' ≤ (1 + log M') σ(x)`, because `σ(x) ≥ 1`
(`one_le_adelicLogHeight`) and `log M' ≥ 0`.

## Proof of the reduction

Fix the data of the target: `F`, `G`, `K`, `rho`, `hsmooth`, `hcalc`, the family `𝓕`, `Φ` with
`IsLogSquareIntegrableAutomorphicForm`, the Siegel setup `(T, i, ν, T₀, j)`, compact factors `C`,
the threshold `t` and the compact `Ω`. The hypothesis on `Φ` gives the automorphy conditions
(left invariance, smoothness, `K_∞`-finiteness, `𝔷`-finiteness; moderate growth and the central
character are not used) and an exponent `m` with `f = Φ(·.out) / σ_{[G]}^m ∈ L²([G], μG)`, where
`σ_{[G]} = rationalLogHeight F G rho` and `μG` is the quotient of Haar measure by counting
measure. The proof takes this `m` as the exponent of the target. Fix a word `D`.

1. *Inputs.* `AdelicLocalL2DerivativeBoundStatement` gives a compact `S` and `c` with
   `‖D Φ(g)‖ₑ² ≤ c ∫⁻_S ‖Φ(g s)‖ₑ² ds`. `SiegelRationalConjugateCountingStatement`, applied to the
   compact set `E = S S⁻¹`, gives `B ≥ 0` with `#(G(F) ∩ x S S⁻¹ x⁻¹) ≤ B δ(a)` at the Siegel
   points, where `δ = siegelModulus`. The height lemma gives `L ≥ 1` with `σ(x s) ≤ L σ(x)`.
2. *Measurability and finiteness.* The function `y ↦ Φ(y.out)` on `[G]` is measurable, since its
   composite with the quotient map is the continuous function `Φ` (left invariance and
   `out_mk_eq_rational_mul`); `σ_{[G]}` is measurable (`measurable_rationalLogHeight`). So `f` is
   measurable, and `I = ∫⁻ ‖f‖ₑ² dμG` is finite because `f ∈ L²`
   (`lintegral_rpow_enorm_lt_top_of_eLpNorm_lt_top`).
3. *Pointwise comparison.* For `s ∈ S` let `y` be the coset of `x s`. Left invariance gives
   `Φ(y.out) = Φ(x s)`, so `‖Φ(x s)‖ = ‖f(y)‖ σ_{[G]}(y)^m`. By `rationalLogHeight_mk_le` and the
   height lemma, `σ_{[G]}(y) ≤ σ(x s) ≤ L σ(x)`, hence `‖Φ(x s)‖ ≤ (L σ(x))^m ‖f(y)‖`.
4. *Folding.* Left translation by `x` preserves Haar measure, so the pushforward of Haar measure
   on `S` under `s ↦ G(F) x s` is the pushforward of Haar measure on `x S` under the quotient map.
   The Library theorem `LeftCosetSpace.leftCosetSupportMeasure`, with the fundamental domain of
   `LeftCosetSpace.isFundamentalDomain` and `D = x S S⁻¹ x⁻¹` (which contains `a b⁻¹` for
   `a, b ∈ x S`), bounds this pushforward by `#(G(F) ∩ x S S⁻¹ x⁻¹) · μG`.
5. *Assembly.* At a Siegel point `x` with torus coordinate `a`, write `W = (L σ(x))^m`. Then

   `‖D Φ(x)‖ₑ² ≤ c ∫⁻_S W² ‖f(G(F) x s)‖ₑ² ds = c W² ∫⁻ ‖f‖ₑ² d(pushforward)`
   `≤ c W² #(G(F) ∩ x S S⁻¹ x⁻¹) I ≤ c W² B δ(a) I`.

   Converting to real numbers, `‖D Φ(x)‖² ≤ c B I L^{2m} δ(a) σ(x)^{2m}`, and taking square roots,

   `‖D Φ(x)‖ ≤ C_D · √δ(a) · σ(x)^m` with `C_D = √(c B I) · L^m ≥ 0`.

This is the bound of the target with the exponent `m`.

## Relation to the sources

The steps are local control of the derivatives, folding onto `[G]`, a bound on the multiplicity
of the folding, and comparison of the weight on the translated compact set with the height of the
point. The folding step is that of the proof of Mœglin–Waldspurger I.2.5 (b) (right convolution,
then an integral over a translated compact set compared with an integral over the quotient) and of
Bernstein's Key Lemma (Bernstein 1988, §3.4) as Delorme applies it in the proof of
Proposition 3.5 (Delorme 2023, p. 12). The local input differs from Delorme's. Bernstein's Key
Lemma is a Sobolev estimate: it bounds `|f(x)|²` by the local integral of `Q(f)`, the sum of the
squares of the derivatives of `f` of degree at most `k`, against the standard measure
`(Ξ^{[G]})² dx`, and Delorme's proof then uses that every derivative of the form is weighted
square integrable. Here `AdelicLocalL2DerivativeBoundStatement`, which comes from differentiating
Harish-Chandra's smooth kernel and the Cauchy–Schwarz inequality, bounds every derivative by the
local `L²` mass of `Φ` itself, so the proof folds `‖Φ‖²` and uses only the weighted
square-integrability of `Φ`, the hypothesis of the target. The factor `Ξ^{[G]}(x)²` of Bernstein's
standard measure is replaced by the count of `SiegelRationalConjugateCountingStatement`, which
bounds the multiplicity of the folding by a multiple of `δ_{P₀}(a)`.
