# Reduction of weighted moderate growth to a reproducing kernel and a point count

Module `Langlands.Global.AdelicWeightedModerateGrowthReduction` proves

`weightedSquareIntegrableModerateGrowth_of_reduction
  (hR : AdelicReproducingKernelStatement)
  (hC : AdelicRationalConjugateCountingAllPointsStatement.{0}) :
  WeightedSquareIntegrableModerateGrowthStatement`.

`WeightedSquareIntegrableModerateGrowthStatement` (module `AdelicSpectralWitnessReduction`) says
that a left `G(F)`-invariant, smooth, `K_∞`-finite and `𝔷`-finite function `Φ` on `G(𝔸)` with
`y ↦ Φ(y.out) / σ_{[G]}(y)^m` in `L²([G], μG)` has moderate growth for the source norm
`RepresentationGrowth.adelicSourceNorm F G rho`. The two premises are
`AdelicReproducingKernelStatement` (module `AdelicReproducingKernelStatement`; Harish-Chandra
1966, §8, Theorem 1) and `AdelicRationalConjugateCountingAllPointsStatement` (module
`AdelicRationalConjugateCountingAllPointsStatement`; Mœglin–Waldspurger I.2.4, Lemma (a)(i)).
This module proves neither premise. The theorem uses only the axioms `propext`,
`Classical.choice` and `Quot.sound`.

| Declaration | Kind | Source |
| --- | --- | --- |
| `weightedSquareIntegrableModerateGrowth_of_reduction` | theorem (proved) | the proof of Mœglin–Waldspurger I.2.5, Lemma (b) |

The argument is that of the proof of Mœglin–Waldspurger I.2.5, Lemma (b) (*Spectral
decomposition and Eisenstein series*, 1995, printed p. 27, chapter file
`05.2_pp_18_40_Automorphic_forms_growth_constant_terms.pdf`), with the square-integrable function
with a unitary central character replaced by a function in `L²([G], σ_{[G]}^{-2m})`.

## Proof (as implemented)

Write `Γ = G(F)` (`rationalSubgroup F G`), `μ` for `Measure.haar` on `G(𝔸)`,
`q = LeftCosetSpace.mk Γ`, `ht = RepresentationGrowth.adelicHeight F G rho`,
`σ = rationalLogHeight F G rho` and `f(y) = Φ(y.out) / σ(y)^m`, so that `f ∈ L²([G], μG)`.

**Rank zero.** If `N = 0`, the map `RepresentationGrowth.adelicMatrix` into `GL_0(𝔸)` is a closed
embedding (`RepresentationGrowth.isClosedEmbedding_adelicMatrix`), hence injective, and
`GL_0(𝔸)` is trivial; so `G(𝔸)` is a subsingleton and `‖Φ g‖ = ‖Φ 1‖ ≤ (‖Φ 1‖ + 1) · s^0` for the
real power `s^0 = 1`.

**Positive rank.** Let `N > 0`.

1. `hR` gives a continuous compactly supported `A` with `Φ(x) = ∫ Φ(x a) A(a) dμ(a)` for all `x`.
   Put `C = tsupport A`, a compact set. `hC` gives `e` and, for the compact set `C C⁻¹`, a
   constant `B ≥ 0` with `#(Γ ∩ x C C⁻¹ x⁻¹) ≤ B ht(x)^e` (and finiteness) for every `x`. Since
   `ht` is continuous (`continuous_adelicHeight`), it is bounded on `C` by some `L ≥ 1`.
2. *Pointwise bound.* Let `a ∈ C` and `y = q(x a)`. Then `y.out = γ x a` with `γ ∈ Γ`
   (`Quotient.out_eq`, `mk_eq_mk_iff`), so `Φ(y.out) = Φ(x a)` by left invariance. Taking this
   `γ⁻¹` in the infimum defining `σ` gives
   `inf_q ‖q y.out‖ ≤ ‖x a‖ ≤ ht(x a) ≤ ht(x) ht(a) ≤ L ht(x)`, using
   `ht = N^s ‖·‖` with `N^s ≥ 1` (`adelicHeight_eq_scalar_mul_sourceNorm`) and
   `adelicHeight_mul_le`. As `L ht(x) ≥ 1` and `log t ≤ t - 1` (`Real.log_le_sub_one_of_pos`),
   `1 ≤ σ(y) ≤ L ht(x)`. Hence `‖Φ(x a)‖ = ‖f(y)‖ σ(y)^m ≤ (L ht(x))^m ‖f(q(x a))‖`.
3. *Folding.* The pushforward of `μ` restricted to `C` under `a ↦ q(x a)` is at most
   `B ht(x)^e · μG`. Indeed, by left invariance of `μ` it equals the pushforward under `q` of `μ`
   restricted to `x C`; differences `u v⁻¹` of points of `x C` lie in `x C C⁻¹ x⁻¹`; and
   `LeftCosetSpace.leftCosetSupportMeasure`, with the Borel fundamental domain defining `μG`
   (`LeftCosetSpace.isFundamentalDomain`), bounds this pushforward by
   `#(Γ ∩ x C C⁻¹ x⁻¹) · μG`, which is at most `B ht(x)^e · μG` by step 1.
4. *Cauchy–Schwarz.* `norm_integral_mul_comp_le_of_map_restrict_le` (module
   `AdelicWeightedConvolutionEstimate`), applied to `h(a) = ‖A(a)‖` (in `L²(μ|_C)`, being
   continuous with compact support) and to `‖f‖ ∈ L²([G], μG)`, shows that
   `a ↦ ‖A(a)‖ ‖f(q(x a))‖` is integrable and
   `∫ ‖A(a)‖ ‖f(q(x a))‖ dμ(a) ≤ c_A · √(B ht(x)^e) · c_f`, where `c_A` and `c_f` are the two
   `L²` norms; they do not depend on `x`.
5. *Assembly.* By step 2 (the integrand vanishes off `C`),
   `‖Φ(x)‖ ≤ ∫ ‖Φ(x a) A(a)‖ dμ ≤ (L ht(x))^m ∫ ‖A(a)‖ ‖f(q(x a))‖ dμ`, hence by step 4
   `‖Φ(x)‖ ≤ (L ht(x))^m c_A √(B ht(x)^e) c_f`. Since `ht(x) ≥ 1`,
   `√(B ht(x)^e) ≤ √B ht(x)^e`, and with `ht(x) = N^s ‖x‖` this gives
   `‖Φ(x)‖ ≤ K₀ ‖x‖^{m+e}` with `K₀ = L^m c_A √B c_f N^{s(m+e)}`. The moderate growth bound holds
   with `C = K₀ + 1 > 0` and the real exponent `r = m + e`.

No measurability of `σ` is needed: `σ` enters only through the pointwise bound of step 2, and the
integrals of steps 4 and 5 involve `A`, `‖f‖` and `Φ` only.
