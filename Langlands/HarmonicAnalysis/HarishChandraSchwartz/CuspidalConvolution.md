# Convolution of a cuspidal function with a wave packet (Waldspurger, proof of Lemma VIII.2.3)

Lean module: `Langlands.HarmonicAnalysis.HarishChandraSchwartz.CuspidalConvolution`, namespace
`Langlands.HarishChandraSchwartz`. It imports
`Langlands.HarmonicAnalysis.HarishChandraSchwartz.CuspidalWavePacketOrthogonality` (Worker 249):
`ConstantTermIndVanishes` and
`pairing_inducedOrbitWavePacket_eq_zero_of_constantTermInd_eq_zero`; through it the Library's
`Space`, `nu`, `levelSubmodule`, `schwartzSubmodule`, `mem_schwartzSubmodule_iff`,
`Space.coe_mem`, `Space.translate`, `Space.check`, `check_apply`, `constantTermInd`,
`constantTerm`, `convolution`, `convolution_apply`, `pairing`, `pairing_apply` and the wave-packet
data of `InducedOrbitWavePacketPairing`.

## Provenance

J.-L. Waldspurger, *La formule de Plancherel pour les groupes p-adiques, d'après
Harish-Chandra*, J. Inst. Math. Jussieu 2 (2003), 235–333, DOI 10.1017/S1474748003000082
(literature id `waldspurger-2003-plancherel`). Printed page numbers; the PDF page is the printed
page minus 234. Overlines in the quotes below were checked on the rendered PDF page 88.

- Lemma VIII.2.3, printed p. 322 (PDF p. 88), and its proof are quoted in
  `CuspidalWavePacketOrthogonality.md`. The steps formalized here: "Il suffit de prouver que si
  `(𝒪, P) ∈ Θ`, `P ≠ G`, et si `ψ ∈ C^∞(𝒪, P)`, on a `f_1 ∗ f_ψ = f_ψ ∗ f_1 = 0`. Soit `g ∈ G`,
  notons `f'_1` la fonction définie par `f'_1(h) = \overline{f_1(gh^{−1})}`. On a l'égalité
  `(f_1 ∗ f_ψ)(g) = (f'_1, f_ψ)_G`. [...] Mais `f'_1 ∈ °𝒞(G)` d'après le Lemme VIII.2.1, donc
  `\hat{f'_1}(ω, P) = 0` pour tout `ω`. On en déduit `f_1 ∗ f_ψ = 0`. Idem `f_ψ ∗ f_1 = 0`."
- Remark VIII.2.2, printed p. 322 (PDF p. 88), lists the symmetries `(°f)ˇ = °(f̌)`,
  `\overline{°f} = °(\bar f)`, `(°f)χ = °(fχ)` of `°𝒞(G)`; the source uses the corresponding
  invariance of `°𝒞(G)` for `f'_1`.

The abstraction, the hypotheses and the proof route are internal to this project.

## Relation to the source

- `IsUnipotentCuspidal ν f` (`∫_U f(x u y) dν(u) = 0` for all `x, y ∈ G`) stands for "the
  constant term of every two-sided translate of `f` along `P = M U` vanishes", i.e.
  `f^{(P),Ind} = 0` (`constantTermIndVanishes_of_isUnipotentCuspidal` and
  `isUnipotentCuspidal_of_constantTermIndVanishes` prove the equivalence for `f ∈ 𝒞(G)`). It is one of the conditions defining `°𝒞(G)` through Lemma
  VIII.2.1 (one for each proper `P`); `°𝒞(G)` itself is not formalized.
- The source obtains `f'_1 ∈ °𝒞(G)` from Lemma VIII.2.1 and the symmetries of `°𝒞(G)`; here the
  condition `IsUnipotentCuspidal` is transferred directly to `h ↦ \overline{f_1(g h^{−1})}` and
  `h ↦ \overline{f_1(h^{−1} g)}` (`isUnipotentCuspidal_conj_mul_inv`,
  `isUnipotentCuspidal_conj_inv_mul`), using the inversion invariance of `ν` (true for the Haar
  measure of the unimodular group `U`; here an explicit instance hypothesis).
- The wave packet `f_ψ` is `inducedOrbitWavePacket` with a weight `w` in place of `µ(ω)` and the
  hypotheses of `InducedOrbitWavePacketPairing`, as in `CuspidalWavePacketOrthogonality`. The
  hypothesis `hint` (absolute convergence in Lemma VII.1.2) is required for the function
  `f'_1`, resp. `f''_1`, at the given `g`.
- Lemma VIII.2.3 itself (`f_1 ∗ f_2 = f_1 ∗ °f_2`) needs `°f_2 = f_2 − κ(ψ)` with the map `κ` of
  VI.3 and is not formalized; the module proves the vanishing `f_1 ∗ f_ψ = f_ψ ∗ f_1 = 0` for the
  wave packets of one orbit of one `P`.

## Contents

### Complex conjugation on `𝒞(G)`

Section variables: a group `G` with a topology, `[IsTopologicalGroup G]`,
`[Nonempty (CompactOpenSubgroup G)]`, weights `Ξ σ : G → ℝ`.

- `nu_complexConj r f`: `nu Ξ σ r (fun g => conj (f g)) = nu Ξ σ r f` (for any type `G`).
- `complexConj_mem_levelSubmodule`: `f ∈ levelSubmodule Ξ σ H → (fun g => conj (f g)) ∈
  levelSubmodule Ξ σ H`.
- `complexConj_mem_schwartzSubmodule`: the same for `schwartzSubmodule Ξ σ`.
- `Space.complexConj f` (definition): `g ↦ conj (f g)` as an element of `Space Ξ σ`, with
  `Space.complexConj_apply`.

### Cuspidality along `U`

Section variables: `G` with a topology, `[IsTopologicalGroup G]`, `[MeasurableSpace G]`,
`[BorelSpace G]`, `[Nonempty (CompactOpenSubgroup G)]`, subgroups `M U`, a measure `ν` on `U`,
`δ : M →* ℝ≥0ˣ`, weights `Ξ σ`, `ΞM σM`.

- `IsUnipotentCuspidal ν f` (definition), for `f : G → ℂ`:
  `∀ x y : G, ∫ u : U, f (x * u * y) ∂ν = 0`.
- `constantTermIndVanishes_of_isUnipotentCuspidal hD hE ht htM`: for
  `hD : ConstantTermData ν δ`, `hE : ConstantTermEstimate ν δ Ξ σ ΞM σM`,
  `ht : TranslationWeights Ξ σ`, `htM : TranslationWeights ΞM σM` and `f : Space Ξ σ` with
  `hf : IsUnipotentCuspidal ν f`: `ConstantTermIndVanishes hD hE ht htM f`.
- `isUnipotentCuspidal_of_constantTermIndVanishes hD hE ht htM`: the converse, for
  `f : Space Ξ σ` with `hf : ConstantTermIndVanishes hD hE ht htM f`:
  `IsUnipotentCuspidal ν f`.
- `isUnipotentCuspidal_conj_mul_inv g hf`: for `[MeasurableInv U]`, `[ν.IsInvInvariant]`,
  `g : G` and `hf : IsUnipotentCuspidal ν f`:
  `IsUnipotentCuspidal ν (fun h => conj (f (g * h⁻¹)))`.
- `isUnipotentCuspidal_conj_inv_mul g hf`: the same for `fun h => conj (f (h⁻¹ * g))`.

### Convolutions as pairings

For a group `G` with `[MeasurableSpace G]`, `[MeasurableMul G]`, `[MeasurableInv G]`:

- `convolution_eq_conj_pairing μ f₁ F g`: for `μ` with `[μ.IsMulLeftInvariant]` and
  `[μ.IsInvInvariant]`,
  `convolution μ f₁ F g = conj (pairing μ F fun h => conj (f₁ (g * h⁻¹)))`.
- `convolution_eq_conj_pairing_right μ F f₁ g` (any measure, no measurability class):
  `convolution μ F f₁ g = conj (pairing μ F fun h => conj (f₁ (h⁻¹ * g)))`.

### The vanishing in the proof of Lemma VIII.2.3

Section variables: those of the section `Pairing` of `InducedOrbitWavePacketPairing` (listed in its
Markdown), with `Ξ = xi hP₀K δ₀`.

- `convolution_inducedOrbitWavePacket_eq_zero`: hypotheses — all hypotheses of
  `pairing_inducedOrbitWavePacket_eq_zero_of_constantTermInd_eq_zero` except `f`, `hint` and
  `h0` (that is `[SigmaFinite μG]`, `[IsFiniteMeasure ρ]`, `hLaurent`, `he`, `hwm`, `b`, `hwb`,
  `hδU`, `hL`, `hMK`, `hδ₀`, `hcoeff`, `q`, `[Nonempty (CompactOpenSubgroup M)]`, `μL` with its
  invariance instances, `ΞM σM`, `hwM`, `hTM`, `hΞM`, `hσM`, `νU` with its invariance instances,
  `hD`, `hνU`, `hE`, `ht`, `htM`, `hμK`, `[MeasurableInv M]`, `[μL.IsInvInvariant]`,
  `[SFinite μL]`, `[SFinite νU]`, `hPKiw`, `hMKμ`, `hUK`); further `[MeasurableInv U]`,
  `[νU.IsInvInvariant]`, `f₁ : Space (xi hP₀K δ₀) σ` with `hcusp : IsUnipotentCuspidal νU f₁`,
  `g : G`, and `hint : ∀ A ψ, Integrable (fun x : G × K => conj (integrand … x.1 ψ x.2) *
  f'₁ x.1) (μG.prod (CompactInduction.measure K hK))` for
  `f'₁ = Space.complexConj (Space.translate ht g⁻¹ 1 (Space.check hΞ hσ f₁))`
  (`h ↦ \overline{f₁(g h⁻¹)}`). Conclusion:
  `convolution μG f₁ (inducedOrbitWavePacket … q) g = 0`.
- `convolution_inducedOrbitWavePacket_left_eq_zero`: the same hypotheses with
  `f''₁ = Space.complexConj (Space.translate ht 1 g (Space.check hΞ hσ f₁))`
  (`h ↦ \overline{f₁(h⁻¹ g)}`) in `hint`. Conclusion:
  `convolution μG (inducedOrbitWavePacket … q) f₁ g = 0`.

## Proof

`nu_complexConj`: `‖conj z‖ = ‖z‖`. The membership lemmas follow (bi-invariance is preserved
pointwise), with `mem_schwartzSubmodule_iff` for `𝒞(G) = ⋃_H 𝒞_H`.

`constantTermIndVanishes_of_isUnipotentCuspidal`: the value of `f^{(P),Ind}(g₁, g₂)` at `m` is
`δ(m)^{1/2} ∫_U f(g₂⁻¹ m u g₁) dν(u)`, which is `δ(m)^{1/2}` times the cuspidal integral for
`x = g₂⁻¹ m`, `y = g₁`.

`isUnipotentCuspidal_of_constantTermIndVanishes`: evaluate `f^{(P),Ind}(y, x⁻¹) = 0` at `m = 1`,
where `δ(1)^{1/2} = 1`.

`isUnipotentCuspidal_conj_mul_inv`: `g (x u y)⁻¹ = (g y⁻¹) u⁻¹ x⁻¹`; the integral of the conjugate
is the conjugate of the integral (`integral_conj`) and `u ↦ u⁻¹` preserves `ν`
(`integral_inv_eq_self`). `isUnipotentCuspidal_conj_inv_mul`: `(x u y)⁻¹ g = y⁻¹ u⁻¹ (x⁻¹ g)`.

`convolution_eq_conj_pairing`: `∫ f₁(h) F(h⁻¹ g) dμ(h) = ∫ f₁(g h) F(h⁻¹) dμ(h)` (left invariance,
`integral_mul_left_eq_self`) `= ∫ f₁(g h⁻¹) F(h) dμ(h)` (inversion invariance), which is the
conjugate of `∫ conj(F(h)) conj(f₁(g h⁻¹)) dμ(h)`, the pairing of `F` with
`h ↦ conj(f₁(g h⁻¹))` (`integral_conj`, `Complex.conj_conj`).
`convolution_eq_conj_pairing_right` is the same identity without substitution:
`∫ F(h) f₁(h⁻¹ g) dμ(h)` is the conjugate of `∫ conj(F(h)) conj(f₁(h⁻¹ g)) dμ(h)`.

`convolution_inducedOrbitWavePacket_eq_zero`: the function `f'₁` equals
`h ↦ \overline{f₁(g h⁻¹)}` (`Space.translate_apply`, `check_apply`), so it is cuspidal; by
`constantTermIndVanishes_of_isUnipotentCuspidal` it satisfies `ConstantTermIndVanishes`, so
`(f_ψ, f'₁)_G = 0` by `pairing_inducedOrbitWavePacket_eq_zero_of_constantTermInd_eq_zero`, and
`convolution_eq_conj_pairing` gives `(f₁ ∗ f_ψ)(g) = conj 0 = 0`. The left version uses `f''₁`
and `convolution_eq_conj_pairing_right`.
