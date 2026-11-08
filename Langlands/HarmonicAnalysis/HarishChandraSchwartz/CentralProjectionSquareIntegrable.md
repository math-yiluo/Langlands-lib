# Square integrability of `p_χ f` on `A_G \ G` (Waldspurger, proofs of Proposition VIII.4.1 and Theorem VIII.4.2)

Lean module: `Langlands.HarmonicAnalysis.HarishChandraSchwartz.CentralProjectionSquareIntegrable`,
namespace `Langlands.HarishChandraSchwartz`. It imports:

- `Langlands.HarmonicAnalysis.HarishChandraSchwartz.KernelQuotient` (Worker 249) and through it
  `CentralProjection` (`centralProjection`, `CentralWeights` with `exists_lintegral_lt_top` and
  `lintegral_enorm_le`, `IsUnitaryCharacter`, `centralProjection_mul_left`,
  `IsBiInvariant.centralProjection`), `Langlands.Analysis.Local.QuotientWeilKernel`
  (`orbitKernel`, `lintegral_orbitKernel`), `QuotientMeasure` (`IsCompatible`), the
  `LeftQuotient` carrier with `descend`, `Basic` (`nu`, `norm_le_of_nu`, `levelSubmodule`,
  `schwartzSubmodule`, `mem_schwartzSubmodule_iff`), `TestFunctions`
  (`IsBiInvariant.isLocallyConstant`) and `Convolution` (`continuous_of_mem_levelSubmodule`);
- `Langlands.HarmonicAnalysis.HarishChandraSchwartz.L2`: `L2Weights`.

## Provenance

J.-L. Waldspurger, *La formule de Plancherel pour les groupes p-adiques, d'après
Harish-Chandra*, J. Inst. Math. Jussieu 2 (2003), 235–333, DOI 10.1017/S1474748003000082
(literature id `waldspurger-2003-plancherel`). Printed page numbers; the PDF page is the printed
page minus 234. The overlines in the quotes below were checked on the rendered PDF pages 94
and 97.

- Proof of Proposition VIII.4.1, printed p. 328 (PDF p. 94): "Pour `f₁, f₂ ∈ p_χ(°𝒞_H)`,
  posons `(f₁, f₂)_{A_G\G} = ∫_{A_G\G} \overline{f₁(g)} f₂(g) dg`. L'intégrale est absolument
  convergente. En effet il existe un sous-ensemble compact `Γ` de `G` tel que `G¹Γ` se projette
  surjectivement sur `A_G \ G`. D'autre part, on vérifie aisément que pour tout
  `f ∈ p_χ(°𝒞(G))` et tout `r ∈ ℝ`, il existe `c > 0` tel que, pour tout `g ∈ G¹`, on ait
  l'inégalité `|f(g)| ⩽ cΞ(g)(1 + σ(g))^{−r}`. Cela assure la convergence."
- Proof of Theorem VIII.4.2, printed p. 331 (PDF p. 97): "D'où l'égalité
  `(f₁, ρ(g)f₂)_{A_G\G} = (p_χ(\check{\bar φ}₁ ∗ φ₂))(g)`. (2) En particulier cette fonction est
  de carré intégrable sur `A_G \ G`."
- Definition of `p_χ`, printed p. 327 (PDF p. 93): "`(p_χ f)(g) = ∫_{A_G} χ^{−1}(a) f(ag) da`.
  L'intégrale est absolument convergente."
- Lemma II.1.5, printed p. 252 (PDF p. 18): "Il existe `d ∈ ℕ` tel que l'intégrale
  `∫_G Ξ(g)²(1 + σ(g))^{−d} dg` soit convergente."

The abstraction, the hypotheses and the proof route are internal to this project.

## Relation to the source

- The module proves the square integrability on `A \ G` of `p_χ f` for every `f ∈ 𝒞(G)`, not
  only for `f ∈ °𝒞(G)`. This contains the absolute convergence of `(f₁, f₂)_{A_G\G}` for
  `f₁, f₂ ∈ p_χ(°𝒞_H)` (p. 328) and the square integrability of
  `(f₁, ρ(g) f₂)_{A_G\G} = p_χ(\check{\bar φ}₁ ∗ φ₂)` (p. 331), the function
  `\check{\bar φ}₁ ∗ φ₂` lying in `𝒞(G)` (Lemma III.6.1).
- The route differs from the source's: instead of the pointwise bound on `G¹` and a compact
  `Γ` with `G¹Γ → A_G \ G` surjective, the proof uses the Weil formula for the compatible
  quotient measure `ν` and Lemma II.1.5 on `G` (the hypothesis `L2Weights μG Ξ σ`). No cell
  decomposition of `A \ G` is needed.
- `A` is an abstract closed subgroup with a right invariant measure `μ_A` (Waldspurger's `A_G`
  with its Haar measure), `G` a second-countable locally compact Hausdorff topological group with
  a measure `μ_G`, and `ν` a measure on `A \ G` (`LeftQuotient A`) compatible with `μ_G` and
  `μ_A` (`IsCompatible`). Functions on `A \ G` are read through the representatives `q̇`
  (`Quotient.out`), as in `KernelQuotient`. `Ξ`, `σ` satisfy `CentralWeights μA Ξ σ` (as in
  `CentralProjection`) and `L2Weights μG Ξ σ`; the elements of `𝒞(G)` are those of
  `schwartzSubmodule Ξ σ`.
- `integrable_centralProjection_mul_conj_out` gives the hypothesis `hprod` of
  `finiteDimensional_of_conjugationIntegralBound` (`KernelFiniteness`) for every space
  `V ⊆ p_χ(𝒞(G))`. The hypothesis `hL2` of `DiscreteCoefficientSpace` is stated on `G ⧸ A`
  with a Haar measure; `exists_memLp_two_centralProjection` gives the same form on `A \ G` with
  `ν`, and the comparison between the two quotients and measures is not made here.

## Contents

Section `Absolute` (a group `G`, a subgroup `A` with a measurable structure and a measure `μ_A`):

- `centralAbsIntegral μA f g` (definition): `∫⁻ a, ‖f (a * g)‖ₑ ∂μA`, the integral
  `∫_{A_G} |f(ag)| da` whose finiteness is the absolute convergence of `(p_χ f)(g)` (p. 327).
- `enorm_centralProjection_le_centralAbsIntegral`: for `hχ : IsUnitaryCharacter χ`,
  `‖p_χ f(g)‖ₑ ≤ centralAbsIntegral μA f g`.
- `centralAbsIntegral_mul_left`: for `[MeasurableMul A]` and `[μA.IsMulRightInvariant]`,
  `centralAbsIntegral μA f (b * g) = centralAbsIntegral μA f g` for `b ∈ A`.

Section `Quotient`: `G` with `[TopologicalSpace G] [IsTopologicalGroup G] [T2Space G]
[LocallyCompactSpace G] [SecondCountableTopology G] [MeasurableSpace G] [BorelSpace G]`, a
subgroup `A` with `hA : IsClosed (A : Set G)`, `[MeasurableSpace A] [BorelSpace A]`,
`[MeasurableSpace (LeftQuotient A)] [BorelSpace (LeftQuotient A)]`, `μA` with `[SFinite μA]
[μA.IsMulRightInvariant] [IsFiniteMeasureOnCompacts μA]`, `μG` with
`[IsFiniteMeasureOnCompacts μG]`, `ν : Measure (LeftQuotient A)`, `Ξ σ : G → ℝ` and
`χ : A →* ℂˣ` (each result uses the subset of these that it needs).

- `lintegral_lintegral_out_eq hA`: for `hν : IsCompatible A μG μA ν` and a measurable
  `F : G → ℝ≥0∞`, `∫⁻ q, ∫⁻ a, F (a * q.out) ∂μA ∂ν = ∫⁻ g, F g ∂μG`.
- `continuous_out_of_invariant`: for a topological space `X`, a continuous `P : G → X` with
  `P (b * g) = P g` for `b ∈ A`, the function `q ↦ P q.out` on `A \ G` is continuous.
- `lintegral_enorm_centralProjection_out_sq_lt_top hA`: for `[MeasurableMul A]`, `hν`,
  `hw : CentralWeights μA Ξ σ`, `hL : L2Weights μG Ξ σ`, `hχ`, a measurable `f` (`hfm`) with
  `hf : ∀ r, nu Ξ σ r f < ⊤`: `∫⁻ q, ‖p_χ f(q.out)‖ₑ ^ 2 ∂ν < ⊤`.
- `continuous_centralProjection`: for `hAc : A ≤ Subgroup.center G`, a
  compact open subgroup `H` and `f ∈ levelSubmodule Ξ σ H`, `p_χ f` is continuous.
- `norm_centralProjection_mul_left`: for `[MeasurableMul A]`, `[μA.IsMulRightInvariant]` and
  `hχ`, `‖p_χ f(b g)‖ = ‖p_χ f(g)‖` for `b ∈ A`.
- `exists_memLp_two_centralProjection hA`: for `[MeasurableMul A]`,
  `[Nonempty (CompactOpenSubgroup G)]`, `hν`, `hAc`, `hw`, `hL`, `hχ` and
  `f ∈ schwartzSubmodule Ξ σ`: there is `F : LeftQuotient A → ℝ` with `MemLp F 2 ν` and
  `F (Quotient.mk _ g) = ‖p_χ f(g)‖` for every `g`.
- `integrable_centralProjection_mul_conj_out hA`: for `[MeasurableMul A]`,
  `[Nonempty (CompactOpenSubgroup G)]`, `hν`, `hAc`, `hw`, `hL`, `hχ` and
  `f₁ f₂ ∈ schwartzSubmodule Ξ σ`: `q ↦ p_χ f₁(q.out) * conj (p_χ f₂(q.out))` is integrable for
  `ν`.

## Proof

`lintegral_lintegral_out_eq`: `lintegral_orbitKernel`, with the orbit measure at `q = A q̇` the
image of `μ_A` under `a ↦ a q̇` (`lintegral_map`).

`lintegral_enorm_centralProjection_out_sq_lt_top`: with `Φ = centralAbsIntegral μA f`,
`|p_χ f| ≤ Φ` and `Φ(a q̇) = Φ(q̇)`, so
`Φ(q̇)² = ∫_A |f(a q̇)| Φ(a q̇) da`; by the Weil formula
`∫_{A\G} |p_χ f(q̇)|² dν ≤ ∫_G |f| Φ dμ_G` (`Φ` is measurable as a parametric lower integral).
Choose `s ≥ 0` with `I = ∫_A (1 + σ(a))^{-s} da < ∞` (`CentralWeights.exists_lintegral_lt_top`)
and `d` with `∫_G Ξ² (1 + σ)^{-d} < ∞` (`L2Weights.square`). Then
`|f(g)| ≤ ν_{s+d}(f) Ξ(g) (1 + σ(g))^{-s-d}` (`norm_le_of_nu`) and
`Φ(g) ≤ ν_s(f) Ξ(g) (1 + σ(g))^s I` (`CentralWeights.lintegral_enorm_le`), so
`|f| Φ ≤ ν_{s+d}(f) ν_s(f) I Ξ² (1 + σ)^{-d}`, whose integral is finite.

`continuous_centralProjection`: `p_χ f` is bi-invariant under `H` (`IsBiInvariant.centralProjection`),
hence locally constant.

`exists_memLp_two_centralProjection`: `F` is the descent of `‖p_χ f‖`, which is `A`-invariant;
read through representatives it is continuous (`continuous_out_of_invariant`), hence
measurable, and its `L²` norm is finite by the previous result.

`integrable_centralProjection_mul_conj_out`: the product is `A`-invariant (`|χ(b)| = 1`), so it
is continuous on `A \ G`; its absolute value is at most `|p_χ f₁(q̇)|² + |p_χ f₂(q̇)|²`, whose
integral is finite.
