# The Fourier transform of a wave packet (Proposition VII.2.1, `M = G`)

Lean module: `Langlands.HarmonicAnalysis.HarishChandraSchwartz.RationalOrbitWavePacketFourier`,
namespace `Langlands.HarishChandraSchwartz` (the separation lemma is
`Langlands.InvariantPositiveForm.eq_of_forall_inner_eq`). It imports:

- `Langlands.HarmonicAnalysis.HarishChandraSchwartz.RationalOrbitWavePacketPairing` (Worker 249,
  accepted candidate `98f5e360`, which replaces the rejected `c992cfbd` and keeps its
  declarations unchanged): the wave packet `rationalOrbitWavePacket` (`f_ψ` for `M = G`),
  `integral_conj_mul_rationalOrbitWavePacket_eq_zero` and
  `integral_conj_mul_rationalOrbitWavePacket_of_mem` (the pairing `(E^G_G ψ', f_ψ)_G`),
  `isSquareIntegrableModCentralSubgroup_out`, `out_representation_central`; through its imports
  the orbit `discreteSeriesOrbit`, `rationalNormCharacters`, the I.1 orbit measure,
  `discreteSeriesFormalDegree` with `discreteSeriesFormalDegree_pos`,
  `isUnitarizable_of_isSquareIntegrable`, `normalLeftQuotientHomeomorph`, `IsCompatible`,
  `rationalCommonNormKernel` (`G¹`) and the local instances on `G(F)` listed in its Markdown;
- `Langlands.HarmonicAnalysis.HarishChandraSchwartz.FourierTransform`: the Fourier transform
  `coefficientFourierTransform A hw hA hT hΞ hσ d f = d • schwartzActionTensor … (Space.check … f)`
  (Waldspurger's `f̂ = d · π(f̌)` of VII.1, `coefficientFourierTransform_apply`) and
  `integral_conj_coefficientTensorMap_mul`
  (`∫_G conj((E ψ)(g)) f(g) dg = (ψ, π(f̌))_b`, the computation in the proof of Lemma VII.1.1
  (ii)), `integrable_conj_coefficientTensorMap_mul`; through its imports `Space Ξ σ` (the
  Harish-Chandra Schwartz space `C(G)` for weight functions `Ξ`, `σ`), `L2Weights`,
  `HasTemperedCoefficients`, `CoefficientTensor`, `coefficientTensorMap`,
  `coefficientTensorInvariantForm` and `InvariantPositiveForm` (with its
  `toInnerProductCore`).

## Provenance

J.-L. Waldspurger, *La formule de Plancherel pour les groupes p-adiques, d'après
Harish-Chandra*, J. Inst. Math. Jussieu 2 (2003), 235–333, DOI 10.1017/S1474748003000082.

- Proposition VII.2.1, printed p. 317 (PDF p. 83): "Soient `ψ ∈ C^∞(O, P)` et `ω' ∈ E₂(M)`. On a
  l'égalité `f̂_ψ(ω', P) = γ(G|M) c(G|M)² ∑_{s ∈ W(G|M) ; s⁻¹ω' ∈ O} ⁰c_{P|P}(s, s⁻¹ω')
  ψ_{s⁻¹ω'}`."
- Its proof, case `M = G`, printed p. 318 (PDF p. 84): "On obtient `(E^G_G ψ', f_ψ)_G` = `0`, si
  `ω' ∉ O`, `(ψ', ψ_{ω'})`, si `ω' ∈ O`. En comparant avec l'égalité (ii) du Lemme VII.1.1, on
  obtient la formule de l'énoncé."
- Lemma VII.1.1 (ii), printed p. 314 (PDF p. 80): `(E_P^G ψ, f)_G = (ψ, f̂(ω, P))`.
- VII.1, printed p. 313 (PDF p. 79): `f̂(ω, P)` is `d(ω)` times the element `π(f̌)` of
  `L(ω, P)`.

This module formalizes that comparison for `M = G`. The separation lemma and the generic theorem
are derived for the proof; `rationalOrbitSectionExtension` is the right side of Proposition
VII.2.1 for `M = G`, and `coefficientFourierTransform_rationalOrbitWavePacket` is the
proposition for `M = G` under the hypotheses listed below.

### Correspondence with the source

- For `M = G`: `W(G|G) = {s ∈ W^G ; s · G = G}/W^G = {1}` (printed p. 276, PDF p. 42);
  `γ(G|G) = mes(H)⁻¹ mes(G ∩ H) = 1` by the formula for `γ(P)` with `U = {1}` and no roots, and
  `c(G|G) = γ(G|G)⁻¹ = 1` (an empty product), printed pp. 240–241 (PDF pp. 6–7);
  `⁰c_{G|G}(1, ω) = c_{G|G}(1, ω)⁻¹ c_{G|G}(1, ω)` is the identity (V.3, printed p. 295, PDF
  p. 61). So the right side of Proposition VII.2.1 is `ψ_{ω'}` if `ω' ∈ O` and the empty sum `0`
  otherwise. This is `rationalOrbitSectionExtension s hs mu omega ψ omega'`.
- As in `RationalOrbitWavePacketPairing`, a discrete-series class `ω'` is read through its chosen
  representative `Quotient.out ω'`, the section `ψ` assigns to each `ω ∈ O` a
  `CoefficientTensor` of the chosen representative of `ω`, and
  `f̂_ψ(ω', G)` is `coefficientFourierTransform (Quotient.out ω') … d(ω') f` with
  `d(ω') = discreteSeriesFormalDegree … ω'`.
- `f_ψ ∈ C(G)` is a hypothesis: `f : Space Ξ σ` with `⇑f = rationalOrbitWavePacket … ψ`.
- `(ψ', ψ_{ω'})` is `d(ω')⁻¹ (ψ', ψ_{ω'})_b` (V.2), and the Fourier transform of VII.1 carries the
  factor `d(ω')`; the two cancel, which is why the theorem on the orbit fixes `d = d(ω')`.
- The factor `μA(A_G ∩ G¹)` from the Fourier inversion over `A_G` is kept: Waldspurger
  normalizes `mes(A_G ∩ K) = 1` (I.1), and the relation between `A_G ∩ K` and `A_G ∩ G¹` is not
  used here.

## Scope and hypotheses

### Separation lemma

`eq_of_forall_inner_eq b h`: `H` a monoid, `V` a complex vector space with a representation `ρ`,
`b` an `InvariantPositiveForm ρ`, and `h : ∀ x, b.inner x y = b.inner x z`.

### Generic section

`G` a topological group with a measurable structure, `OpensMeasurableSpace`, `MeasurableMul`,
`MeasurableInv`, and a compact open subgroup; `μ` on `G` left, right and inversion invariant;
`Ξ σ : G → ℝ`; `A` a smooth complex representation of `G`; `hw : L2Weights μ Ξ σ`;
`hA : IsAdmissible A.representation`; `hT : HasTemperedCoefficients Ξ σ A.representation`;
`hΞ : ∀ g, Ξ g⁻¹ = Ξ g`; `hσ : ∀ g, σ g⁻¹ = σ g`.

- `coefficientFourierTransform_eq_smul_of_forall_integral A hw hA hT hΞ hσ b d f k φ h`: `b` a
  positive invariant form on `A`, `d : ℝ`, `f : Space Ξ σ`, `k : ℂ`, `φ : CoefficientTensor A`,
  and `h`: for every `ψ'`, `∫_G conj((E ψ')(g)) f(g) dμ = k (ψ', φ)_b`, where `( , )_b` is
  `coefficientTensorInvariantForm A CompactOpenSubgroup.cofinal hA b`.

### Rational section

`F` a nonarchimedean local field (`Field`, `ValuativeRel`, `TopologicalSpace`,
`IsNonarchimedeanLocalField`); `G` an affine group scheme over `F` locally of finite type, with
the local instances on `G(F)` of `RationalOrbitWavePacketPairing` (rational-point topology,
nonarchimedean topological group, `T2Space`, `LocallyCompactSpace`, `SecondCountableTopology`, a
compact open subgroup). `T` an affine commutative group scheme, `s : T → G` with
`hs : GroupScheme.IsCentral s`, `A_G = s(T(F))`, a measurable structure on `G(F)/A_G` with a
measure `mu`, and `hindex : (RenardCartan.splitValuationImage s).FiniteIndex`.

- `rationalOrbitSectionExtension s hs mu omega ψ omega'`, `rationalOrbitSectionExtension_of_mem
  s hs mu omega ψ omega' homega'` (`homega' : omega' ∈ O`) and
  `rationalOrbitSectionExtension_of_notMem s hs mu omega ψ omega' homega'`
  (`homega' : omega' ∉ O`): `mu` Haar, `omega` a discrete-series class with orbit `O`, `ψ` a
  section over `O`, `omega'` a discrete-series class.

The three Fourier-transform theorems further assume measurable structures with `BorelSpace` on
`G(F)`, `A_G` and `A_G\G(F)`, and `BorelSpace` on `G(F)/A_G`. Each of
`coefficientFourierTransform_rationalOrbitWavePacket_eq_zero s hs mu hindex hG hAc omega μA μG
ν hν hνμ ψ hcont hintA hw hΞ hσ f hf omega' homega' hT d`,
`coefficientFourierTransform_rationalOrbitWavePacket_of_mem … hf omega' homega' hT` and
`coefficientFourierTransform_rationalOrbitWavePacket … hf omega' hT` takes:

- `hG : GroupScheme.IsConnectedReductive G`;
- `hAc : IsClosed (A_G : Set G(F))`;
- `mu` Haar and inversion invariant;
- `omega`, a discrete-series class (square integrable modulo `A_G` for `mu`), with orbit `O`;
- `μA` on `A_G`: `SFinite`, left invariant, right invariant, finite on compacts;
- `μG` on `G(F)`: finite on compacts, left, right and inversion invariant;
- `ν` on `A_G\G(F)` with `hν : IsCompatible A_G μG μA ν` and
  `hνμ : ν.map (normalLeftQuotientHomeomorph A_G) = mu`;
- the section `ψ` with `hcont`: for every `g`, `ω ↦ (E^G_G ψ_ω)(g)` is continuous on `O`;
- `hintA`: for every `g`, `a ↦ f_ψ(a g)` is `μA`-integrable;
- weights `Ξ σ` on `G(F)` with `hw : L2Weights μG Ξ σ`, `hΞ : ∀ g, Ξ g⁻¹ = Ξ g`,
  `hσ : ∀ g, σ g⁻¹ = σ g`;
- `f : Space Ξ σ` with `hf : ⇑f = rationalOrbitWavePacket s hs mu hindex omega ψ`;
- `omega'` a discrete-series class and
  `hT : HasTemperedCoefficients Ξ σ (Quotient.out omega').representation`;

and in addition `homega' : omega' ∉ O` and any `d : ℝ` for `_eq_zero`, and
`homega' : omega' ∈ O` for `_of_mem`. In `_of_mem` and in the combined theorem the factor of the
Fourier transform is `d = discreteSeriesFormalDegree … omega'`.

## Definitions

- `rationalOrbitSectionExtension s hs mu omega ψ omega'` is `ψ ⟨omega', h⟩` if
  `h : omega' ∈ O` and `0` otherwise.

## Results

- `InvariantPositiveForm.eq_of_forall_inner_eq`: if `b(x, y) = b(x, z)` for every `x`, then
  `y = z`.
- `coefficientFourierTransform_eq_smul_of_forall_integral`: under `h`, `f̂ = (d k) • φ` for the
  Fourier transform with factor `d`.
- `rationalOrbitSectionExtension_of_mem` / `_of_notMem`: the two values of the extension.
- `coefficientFourierTransform_rationalOrbitWavePacket_eq_zero`: if `ω' ∉ O`, the Fourier
  transform of `f` at the chosen representative of `ω'` is `0`, for every factor `d`.
- `coefficientFourierTransform_rationalOrbitWavePacket_of_mem`: if `ω' ∈ O`,
  `f̂(ω') = μA(A_G ∩ G¹) • ψ_{ω'}`.
- `coefficientFourierTransform_rationalOrbitWavePacket` (Proposition VII.2.1 for `M = G`, with
  the factor `μA(A_G ∩ G¹)`): `f̂(ω') = μA(A_G ∩ G¹) • rationalOrbitSectionExtension … ψ ω'` for
  every discrete-series class `ω'`.

Here `A_G ∩ G¹` is `Subtype.val ⁻¹' rationalCommonNormKernel G` and `f̂(ω')` is
`coefficientFourierTransform (Quotient.out omega') hw … hT hΞ hσ d f`, with admissibility of the
chosen representative from `isSquareIntegrableModCentralSubgroup_out`.

## Proof notes

1. Separation: with the inner product core of `b`, `b(y - z, y - z) = b(y - z, y) - b(y - z, z)
   = 0` by `h`, so `y - z = 0` by definiteness.
2. Generic theorem: by `integral_conj_coefficientTensorMap_mul` and `h`,
   `(ψ', π(f̌))_b = k (ψ', φ)_b = (ψ', k φ)_b` for every `ψ'`; step 1 for the positive form
   `coefficientTensorInvariantForm … b` gives `π(f̌) = k φ`, and
   `coefficientFourierTransform_apply` gives `f̂ = d • k • φ`.
3. Off the orbit: the chosen representative of `ω'` is unitarizable
   (`isUnitarizable_of_isSquareIntegrable`), giving `b`; step 2 with `k = 0`, `φ = 0`, where `h`
   is `integral_conj_mul_rationalOrbitWavePacket_eq_zero` (integrability from
   `integrable_conj_coefficientTensorMap_mul`, rewritten by `hf`).
4. On the orbit: step 2 with `k = μA(A_G ∩ G¹) d(ω')⁻¹` and `φ = ψ_{ω'}`, where `h` is
   `integral_conj_mul_rationalOrbitWavePacket_of_mem`; then `d(ω') k = μA(A_G ∩ G¹)` because
   `d(ω') > 0` (`discreteSeriesFormalDegree_pos`).
5. Combined theorem: case split on `ω' ∈ O`, rewriting `rationalOrbitSectionExtension` by
   `_of_mem` or `_of_notMem` and applying step 4 or step 3.

## Open obligations

- `f_ψ ∈ C(G)` (Proposition VI.3.1) is the hypothesis `hf`, with weights `Ξ`, `σ` subject to
  `hw`, `hΞ`, `hσ`; the tempered growth of the coefficients of `ω'` is the hypothesis `hT`. The
  hypotheses `hcont`, `hintA`, and the normalization of the measures are as in
  `RationalOrbitWavePacketPairing` (see the open obligations there).
- The general case of Proposition VII.2.1 (`M ≠ G`, through Proposition VI.4.1 (ii) and Lemma
  VII.1.2) is not addressed.
