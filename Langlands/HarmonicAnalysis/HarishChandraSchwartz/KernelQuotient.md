# The reproducing kernel `α_χ` on `A \ G` (Waldspurger VIII.4.1)

Lean module: `Langlands.HarmonicAnalysis.HarishChandraSchwartz.KernelQuotient`, namespace
`Langlands.HarishChandraSchwartz`. It imports `KernelReproduction` (`kernelAlpha`,
`kernelAlphaChi`, `conj_kernelAlphaChi`, `integral_conj_kernelAlphaChi_mul`),
`SectionReproducingKernel` (`IsSectionReproducingKernel`,
`IsSectionReproducingKernel.finiteDimensional`), the published
`Langlands.Analysis.Local.QuotientWeilKernel` (`orbitKernel`, `orbitKernel_comp`; it brings
`LeftQuotient` and `IsCompatible` from `QuotientMeasure`), `CentralProjection` (through
`KernelReproduction`: `centralProjection`, `centralProjection_mul_left`,
`IsUnitaryCharacter`) and Mathlib's `Probability.Kernel.Composition.IntegralCompProd`
(`ProbabilityTheory.Kernel.integral_comp`, `Measure.comp_eq_comp_const_apply`,
`Measure.ae_integrable_of_integrable_comp`).

## Source

J.-L. Waldspurger, *La formule de Plancherel pour les groupes p-adiques, d'après
Harish-Chandra*, J. Inst. Math. Jussieu 2 (2003), 235–333, DOI
10.1017/S1474748003000082. Printed page numbers; the PDF page is the printed page minus
234. Bars checked on the page images.

- Proposition VIII.4.1, printed p. 327 (PDF p. 93): for every compact open subgroup `H` and
  every `χ ∈ Â_G`, `p_χ(°C_H)` is finite dimensional.
- Its proof, printed p. 328 (PDF p. 94): `α_χ(·, g₂) = p_χ α(·, g₂) ∈ p_χ(°C_H)`; for
  `f₁, f₂ ∈ p_χ(°C_H)`, `(f₁, f₂)_{A_G\G} = ∫_{A_G\G} conj(f₁(g)) f₂(g) dg`, an absolutely
  convergent integral; formula (1), `(α_χ(·, g), f)_{A_G\G} = f(g)`, with the first step
  `(α_χ(·, g), f)_{A_G\G} = ∫_G conj(α_χ(g', g)) φ(g') dg'` for `f = p_χ φ`, `φ ∈ °C_H`.
- Printed pp. 329–330 (PDF pp. 95–96): from (1) and the convergence of
  `∫_{A_G\G} α_χ(g, g) dg` (Corollary VIII.3.2, printed "Corollaire III.3.2" on p. 330), the
  space is finite dimensional.

The module proves the first step of (1) (unfolding the quotient product to an integral over
`G`), combines it with the second step proved in `KernelReproduction`, and derives the
finite dimensionality from `SectionReproducingKernel`, with the analytic inputs as hypotheses.

## Scope: abstract data and explicit hypotheses

The setting is that of the published Weil formula `QuotientWeilKernel`:

- `G` is a Hausdorff, locally compact, second countable topological group with its Borel
  structure (`[T2Space G]`, `[LocallyCompactSpace G]`, `[SecondCountableTopology G]`,
  `[BorelSpace G]`); `μG` is a measure on `G` finite on compacts.
- `A` is a closed subgroup (`hA : IsClosed (A : Set G)`) with its Borel structure and a
  measure `μA` that is s-finite, right invariant and finite on compacts.
- `LeftQuotient A` is the existing quotient by the cosets `A g` with its Borel structure, and
  `ν` a measure on it with `hν : IsCompatible A μG μA ν`: `ν` is nonzero, regular, right
  invariant, and satisfies the Weil formula for compactly supported continuous functions.
  For central `A` this quotient is Waldspurger's `A_G \ G`. Points are read through
  `Quotient.out`, written `q̇` below.
- `χ : A →* ℂˣ`, `H` a subgroup with a measure `μH`, and `E : G → ℂ` (for `°e`) are as in
  `KernelReproduction`.

The hypotheses of each result:

- `integral_integral_out_eq`: `hA`, `[MeasurableMul A]`, `hν`, `hF : Integrable F μG`.
- `integral_centralProjection_mul_conj`: `hA`, `[MeasurableMul A]`, `hν`,
  `hχ : IsUnitaryCharacter χ`, `hK : K(a g) = χ(a) K(g)` for `a ∈ A`, and
  `hint : Integrable (fun g => conj (K g) * φ g) μG`.
- `kernelAlphaChi_mul_left`: `[MeasurableMul A]` and right invariance of `μA`.
- `integrable_conj_kernelAlphaChi_mul`: `[SFinite μG]`, `[SFinite μH]`, `[MeasurableInv A]`,
  `[μA.IsInvInvariant]`, `hAc : A ≤ Subgroup.center G`, `hχ`, `hE : ∀ x, conj (E x) = E x`,
  and the triple integrability `hint` of `KernelReproduction` at `g`.
- `integral_centralProjection_mul_conj_kernelAlphaChi`: all of the above (`hA`, `hν`, the
  instances, `hAc`, `hχ`, `hE`), and for `φ`: left `H`-invariance `hH`,
  `hconv : ∀ x, convolution μG φ E x = (μH Set.univ).toReal * φ x`,
  `hmes : (μH Set.univ).toReal ≠ 0`, and `hint` at `g`.
- `isSectionReproducingKernel_kernelAlphaChi`: `hA`, `hν`, the instances, `hAc`, `hχ`, `hE`,
  `hmes`, and for the space `V`: `hV : IsKernelAlphaChiSpace μG μA χ μH E V`,
  `hKV : ∀ y, (fun g => kernelAlphaChi μA χ μH E g y) ∈ V` (Waldspurger's
  `α_χ(·, y) ∈ p_χ(°C_H)`), and `hprod`: for `f, f' ∈ V`, `q ↦ f(q̇) conj(f'(q̇))` is
  `ν`-integrable (Waldspurger's absolute convergence of `(f₁, f₂)_{A_G\G}`).
- `finiteDimensional_of_kernelAlphaChi`: those of `isSectionReproducingKernel_kernelAlphaChi`
  and `hdiag : Integrable (fun q => (kernelAlphaChi μA χ μH E q̇ q̇).re) ν` (Waldspurger's
  convergence of `∫_{A_G\G} α_χ(g, g) dg`).

## Definitions

- `IsKernelAlphaChiSpace μG μA χ μH E V : Prop`: every `f ∈ V` equals `p_χ φ`
  (`centralProjection μA χ φ`) for some `φ : G → ℂ` that is left invariant under `H`,
  satisfies `convolution μG φ E = mes(H) φ` pointwise, and for every `g` makes
  `(g', a, h) ↦ E(g'⁻¹ h (a g)) φ(g')` integrable for `μG.prod (μA.prod μH)`. For
  `V = p_χ(°C_H)`, `E = °e` and `μH` the restriction of `μG` to `H`, these are the properties
  of `φ ∈ °C_H` used in the proof of (1) (Lemma VIII.2.3, the bi-invariance of `φ`, the
  absolute convergence stated by Waldspurger).

## Results

- `integral_integral_out_eq` (**Weil formula for integrable functions**):
  `∫_{A\G} ∫_A F(a q̇) dμA(a) dν(q) = ∫_G F dμG`.
- `integral_centralProjection_mul_conj`: for `χ`-covariant `K` and unitary `χ`,
  `∫_{A\G} (p_χ φ)(q̇) conj(K(q̇)) dν(q) = ∫_G conj(K(g)) φ(g) dμG(g)`.
- `kernelAlphaChi_mul_left`: `α_χ(b g₁, g₂) = χ(b) α_χ(g₁, g₂)` for `b ∈ A`.
- `integrable_conj_kernelAlphaChi_mul`: `g' ↦ conj(α_χ(g', g)) φ(g')` is `μG`-integrable.
- `integral_centralProjection_mul_conj_kernelAlphaChi` (**formula (1)**):
  `∫_{A\G} (p_χ φ)(q̇) conj(α_χ(q̇, g)) dν(q) = (p_χ φ)(g)`, i.e.
  `(α_χ(·, g), p_χ φ)_{A\G} = (p_χ φ)(g)`.
- `isSectionReproducingKernel_kernelAlphaChi`: `y ↦ α_χ(·, y)` is a reproducing kernel for `V`
  read through `Quotient.out` (`IsSectionReproducingKernel ν Quotient.out V _`).
- `finiteDimensional_of_kernelAlphaChi` (**Proposition VIII.4.1 in abstract form**): `V` is
  finite dimensional.

## Proof notes

- Weil formula: `orbitKernel_comp` identifies `μG` with the composite of the orbit kernel and
  `ν`. For an integrable `F`, `Kernel.integral_comp` (after
  `Measure.comp_eq_comp_const_apply`) writes `∫ F dμG` as the iterated integral over the
  orbit kernel. For `ν`-almost every `q`, `F` is integrable for the orbit measure at `q`
  (`Measure.ae_integrable_of_integrable_comp`); this measure is the image of `μA` under
  `a ↦ a q̇` (`orbitKernel_mk` at `q = ⟦q̇⟧`), and `integral_map` gives `∫_A F(a q̇) dμA`.
- Covariant pairing: apply the Weil formula to `conj(K) φ`. Since
  `conj(K(a g)) = conj(χ(a)) conj(K(g)) = χ(a)⁻¹ conj(K(g))`, the inner integral is
  `conj(K(q̇)) ∫_A χ(a)⁻¹ φ(a q̇) dμA = conj(K(q̇)) (p_χ φ)(q̇)`.
- Covariance of `α_χ(·, g₂) = p_χ α(·, g₂)` is `centralProjection_mul_left`.
- Integrability: the function `F(g', a, h) = χ(a)⁻¹ mes(H)⁻² E(g'⁻¹ h a g) φ(g')` is integrable
  on `G × A × H` by `hint`. Its partial integral over `A × H` is integrable on `G`
  (`Integrable.integral_prod_left`), and equals `conj(α_χ(g', g)) φ(g')` for almost every
  `g'` by `conj_kernelAlphaChi` and Fubini on `A × H`.
- Formula (1): the covariant pairing with `K = α_χ(·, g)`, then
  `integral_conj_kernelAlphaChi_mul`.
- The last two results: the structure fields are `hprod` and formula (1); finiteness is
  `IsSectionReproducingKernel.finiteDimensional`.

## Relation to the Library

- `QuotientWeilKernel` proves the Weil formula for nonnegative measurable functions
  (`lintegral_orbitKernel`); `integral_integral_out_eq` is its extension to integrable complex
  functions, read through representatives. No other Library declaration states it.
- `ReproducingKernel` (`IsReproducingKernel`) records in its open obligations that its
  setting does not reach `p_χ(°C_H)`; this module reaches it through
  `SectionReproducingKernel`.

## Open obligations

The definitions of `°e` and `°C_H` (VIII.2, which depend on Theorem VII.2.5), the verification
of `IsKernelAlphaChiSpace` for `p_χ(°C_H)` (Lemma VIII.2.3, the absolute convergence of the
triple integrals), of `hKV`, of `hprod` (the bound `|f(g)| ≤ c Ξ(g)(1 + σ(g))^{-r}` on `G¹`),
and of `hdiag` (Corollary VIII.3.2 and the computation of `α_χ(g, g)` on printed p. 329), and
the identification of `μH` with the restriction of the Haar measure of `G`, are not proved
here. A compatible measure `ν` exists for a closed subgroup with regular two-sided Haar
measures on `G` and `A` by the published `Langlands.QuotientIntegration.compatibleMeasureExists`;
its comparison with Waldspurger's normalization of the measure on `A_G \ G` is not made here.
