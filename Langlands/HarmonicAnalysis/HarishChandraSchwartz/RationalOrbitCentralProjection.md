# The central projection of a wave packet (Waldspurger, proof of Theorem VIII.4.2, `M = G`)

Lean module: `Langlands.HarmonicAnalysis.HarishChandraSchwartz.RationalOrbitCentralProjection`,
namespace `Langlands.HarishChandraSchwartz`. It imports
`Langlands.HarmonicAnalysis.HarishChandraSchwartz.RationalOrbitWavePacketPairing` (Worker 249):
the wave packet `rationalOrbitWavePacket` with `rationalOrbitWavePacket_apply`,
`coefficientTensorMap_out_mul`, `finite_setOf_rationalOrbitCentralCharacter_eq` and
`integral_rationalOrbitCentralInversion_eq_finsum`; through it `rationalOrbitCentralCharacter`,
`rationalOrbitInversionIntegrand`, the orbit `discreteSeriesOrbit`, the orbit measure
`rationalNormalizedDiscreteSeriesOrbitMeasure`, `rationalCommonNormKernel`,
`coefficientTensorMap` and the local-field and rational-point instances.

## Provenance

J.-L. Waldspurger, *La formule de Plancherel pour les groupes p-adiques, d'après
Harish-Chandra*, J. Inst. Math. Jussieu 2 (2003), 235–333, DOI 10.1017/S1474748003000082
(literature id `waldspurger-2003-plancherel`). Printed page numbers; the PDF page is the printed
page minus 234. Hats and calligraphic letters in the quotes below were checked on the rendered
PDF page 96.

- Before Theorem VIII.4.2, printed p. 330 (PDF p. 96): "Pour `χ ∈ Â_G`, notons `𝓔_2(G)_χ`
  l'ensemble des `ω ∈ 𝓔_2(G)` tels que la restriction `χ_ω` à `A_G` de leur caractère central
  soit égale à `χ`. Posons `𝒜_2(G)_χ = ⊕_{ω ∈ 𝓔_2(G)_χ} 𝒜(ω)`."
- Theorem VIII.4.2, printed p. 330: "Pour tout `χ ∈ Â_G`, on a l'égalité
  `p_χ(°𝒞(G)) = 𝒜_2(G)_χ`."
- Its proof, printed p. 330: "Soit `ω ∈ 𝓔_2(G)_χ`. Notons `𝒪` son orbite pour l'action de
  `Im X(G)`. Soit `ψ ∈ C^∞(𝒪, G)`. D'après le Théorème VII.2.5, on a l'égalité `°f_ψ = f_ψ`,
  donc `f_ψ ∈ °𝒞(G)`. Pour tout `g ∈ G`, on a les égalités
  `(p_χ f_ψ)(g) = ∫_{A_G} χ^{−1}(a) f_ψ(ag) da = ∫_{A_G} χ^{−1}(a) ∫_𝒪 (E^G_G ψ_{ω'})(ag) dω' da
  = ∫_{A_G} χ^{−1}(a) ∫_𝒪 χ_{ω'}(a)(E^G_G ψ_{ω'})(g) dω' da`. Par inversion de Fourier, on
  obtient `(p_χ f_ψ)(g) = Σ_{ω' ∈ 𝒪_χ} (E^G_G ψ_{ω'})(g)`, où
  `𝒪_χ = {ω' ∈ 𝒪; χ_{ω'} = χ}`. C'est un ensemble fini contenant `ω`. Pour tout `ϕ ∈ 𝒜(ω)`, on
  peut trouver `ψ ∈ C^∞(𝒪, G)` tel que `ψ_{ω'} = 0` si `ω' ∈ 𝒪_χ − {ω}` et `E^G_G ψ_ω = ϕ`.
  Pour un tel `ψ`, on a `ϕ = p_χ f_ψ` donc `ϕ ∈ p_χ(°𝒞(G))`. D'où l'inclusion
  `𝒜_2(G)_χ ⊂ p_χ(°𝒞(G))`."

The abstraction, the hypotheses and the proof route are internal to this project.

## Relation to the source

- The setting is that of the section `Rational` of `RationalOrbitWavePacketPairing` (see its
  Markdown): the rational points `G(F)` of an affine group scheme `G` of locally finite type over
  a nonarchimedean local field `F`, a central `s : T → G` whose image is `A_G`, a measure `mu` on
  `G(F)/A_G` and `hindex` (finite index of the split valuation image). The orbit `𝒪` of
  `ω₀ = omega` is `discreteSeriesOrbit`, `χ_ω` is `rationalOrbitCentralCharacter`, the wave packet
  `f_ψ` is `rationalOrbitWavePacket` (with `µ(ω) = 1` for `M = G`), and `(E^G_G ψ_ω)(g)` is
  `coefficientTensorMap _ (ψ ω) g` for a section `ψ` of coefficient tensors of the chosen
  representatives.
- The character `χ ∈ Â_G` is `eta : A_G →* Circle`, assumed continuous; the integral
  `∫_{A_G} η(a⁻¹) f_ψ(a g) dμ_A(a)` is `(p_χ f_ψ)(g)` for a left invariant measure `μ_A` on `A_G`.
  As in `RationalOrbitCentralInversion`, the factor `μ_A(A_G ∩ G¹)` is kept (Waldspurger
  normalizes the measures so that it does not appear).
- `rationalOrbitCentralFiber … omega eta` is `𝒪_χ`.
- Only the continuity of `ω ↦ (E^G_G ψ_ω)(g)` and the integrability of `a ↦ f_ψ(a g)` are
  assumed, for the given `g`, in place of `ψ ∈ C^∞(𝒪, G)`. The existence of a section `ψ` with
  prescribed values (`ψ_{ω'} = 0` on `𝒪_χ − {ω}`, `E^G_G ψ_ω = ϕ`) satisfying these hypotheses,
  and the membership `f_ψ ∈ °𝒞(G)` (which uses Theorem VII.2.5), are not formalized; so the
  inclusion `𝒜_2(G)_χ ⊂ p_χ(°𝒞(G))` itself is not formalized, only the computation of
  `p_χ f_ψ` that yields it.

## Contents

Section variables: those of the section `Rational` of `RationalOrbitWavePacketPairing` (`F`, the
group scheme `G` with `[IsAffine G.X.left]` and `[LocallyOfFiniteType G.X.hom]`, `T` with
`[IsAffine T.X.left]`, `s`, `hs : GroupScheme.IsCentral s`, a measurable structure on
`G(F)/A_G`, `mu`, `hindex`), with the same local instances on `G(F)` (named
`instRationalOrbitCentralProjection1` … `7`).

- `rationalOrbitCentralFiber s hs mu omega eta` (definition), for a Haar `mu`, a discrete-series
  class `omega` and `eta : A_G →* Circle`: the set `{ω ∈ 𝒪 | rationalOrbitCentralCharacter s hs
  mu omega ω = eta}`.
- `integral_central_rationalOrbitWavePacket s hs mu hindex hG`: for
  `hG : GroupScheme.IsConnectedReductive G`, a Haar `mu`, `omega`, measurable and Borel structures
  on `A_G`, a left invariant measure `μA` on `A_G`, `eta` with `Continuous eta`, a section `ψ`,
  `g ∈ G(F)`, `hcont : Continuous (fun ω => coefficientTensorMap _ (ψ ω) g)` and
  `hintA : Integrable (fun a => rationalOrbitWavePacket … ψ (a * g)) μA`:
  `∫ a, (eta a⁻¹ : ℂ) * rationalOrbitWavePacket … ψ (a * g) ∂μA =
  μA(A_G ∩ G¹) * ∑ᶠ ω ∈ rationalOrbitCentralFiber s hs mu omega eta,
  coefficientTensorMap _ (ψ ω) g`, where `A_G ∩ G¹` is the preimage of
  `rationalCommonNormKernel G`.
- `integral_central_rationalOrbitWavePacket_of_vanishing s hs mu hindex hG`: the same data and
  `ω₁ ∈ rationalOrbitCentralFiber s hs mu omega eta` with `ψ ω = 0` for every other
  `ω ∈ rationalOrbitCentralFiber s hs mu omega eta`, and `hcont`, `hintA` for `g`:
  `∫ a, (eta a⁻¹ : ℂ) * rationalOrbitWavePacket … ψ (a * g) ∂μA =
  μA(A_G ∩ G¹) * coefficientTensorMap _ (ψ ω₁) g`.

## Proof

`integral_central_rationalOrbitWavePacket`: pointwise in `a`,
`η(a⁻¹) f_ψ(a g) = η(a⁻¹) ∫_𝒪 (E^G_G ψ_ω)(g) χ_ω(a) dω` (`rationalOrbitWavePacket_apply` and
`coefficientTensorMap_out_mul`: the central character of the chosen representative of `ω` on
`A_G` is `χ_ω`), which is `rationalOrbitInversionIntegrand … (fun ω => (E^G_G ψ_ω)(g)) a`. This
function is integrable (a bounded continuous factor times `hintA`), and
`integral_rationalOrbitCentralInversion_eq_finsum` gives the finite sum.

`integral_central_rationalOrbitWavePacket_of_vanishing`: the fiber is finite
(`finite_setOf_rationalOrbitCentralCharacter_eq`), and only the term `ω₁` of the sum is nonzero
(`Finset.sum_eq_single_of_mem`).
