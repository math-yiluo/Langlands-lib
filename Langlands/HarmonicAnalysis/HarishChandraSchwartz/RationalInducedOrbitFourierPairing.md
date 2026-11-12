# `ψ_f[O, P]` and the pairing of wave packets with `C(G)` on actual points (Waldspurger VII.1, VII.2)

Author: Worker 3642, task `1ef6854b-f0e9-4d96-bbe5-cb8c4b52f927` (revision 1).

Lean module: `Langlands.HarmonicAnalysis.HarishChandraSchwartz.RationalInducedOrbitFourierPairing`,
namespace `Langlands.HarishChandraSchwartz`. It imports:

- `Langlands.HarmonicAnalysis.HarishChandraSchwartz.RationalInducedOrbitWavePacket` (this
  author's Unit 20, candidate `32489085-08ba-4b12-be15-d1eee77e42b3`, review-accepted). It
  provides:
  - the actual wave packet `rationalInducedOrbitWavePacket` and `C^∞(O, P)`
    (`rationalInducedSmoothOrbitSections`);
  - the circle coordinates `leviRationalUnitaryCoordinates`, with
    `leviRationalUnitaryCoordinates_hasLaurent`.

  Through Unit 19 (published) it brings the actual data of `P_I(F)`, `rationalLeviXi`,
  `rationalLeviData`, `compactSpace_subgroupOf_standardLevi`, `rationalMinimalModulus_eq_one` and
  `isUnimodularModulus_standardUnipotentPoints`.
- `Langlands.HarmonicAnalysis.HarishChandraSchwartz.RationalInducedFourierTransform` (this
  author's Unit 22, candidate `f4294d1f-31a6-454a-b620-a27ffd3f9df8`, published). It provides
  `rationalInducedFourierTransform` (`f̂(ω, P)`) and `compactOpenCofinal_standardLevi`. Through
  it come `rationalL2Weights`, `rationalXi_inv`, `rationalHeight_inv`,
  `rationalHasTemperedCoefficients_normalizedInduction`, `IsRationalLeviTempered` and
  `RationalSchwartzSpace`.
- `Langlands.HarmonicAnalysis.HarishChandraSchwartz.InducedOrbitWavePacketPairing` (Worker 249).
  It provides `pairing_inducedOrbitWavePacket_eq_integral_productPairing` (formula (1),
  abstract) and `unitaryOrbitWeightedProductPairing`. Through its imports come:
  - `fourierOrbitSection`, `fourierOrbitSection_apply`, `fourierOrbitSection_mem_coherent` and
    `coherentProductInducedOrbitSections` (`InducedFourierCoherence`);
  - `unitaryOrbitProductPairing`, `pairing`;
  - `unitaryOrbitRepresentative_isDiscreteSeries`, `discreteSeriesOrbitMeasure`.

## Source

J.-L. Waldspurger, *La formule de Plancherel pour les groupes p-adiques, d'après Harish-Chandra*,
J. Inst. Math. Jussieu 2 (2003), 235–333, DOI 10.1017/S1474748003000082 (literature id
`waldspurger-2003-plancherel`, SHA256
`4b6a6162cd0b3863703fb2f65d1698f926caf813114917f2084c16e38f2e30f7`). Page numbers are printed
pages; the PDF page is the printed page minus 234. The author checked the quotations below on the
text of PDF pages 82 and 85.

- VII.1, printed p. 316: "Soit `O` une orbite dans `E_2(M)` pour l'action de `Im X(M)`. Pour
  `f ∈ C(G)`, on définit une fonction `ψ_f[O, P]` sur `O` par: `ψ_f[O, P]_ω = f̂(ω, P)` pour tout
  `ω ∈ O`."
- Proof of Proposition VII.2.2, printed p. 319: "On a l'égalité
  `(f_{ψ'}, f_ψ)_G = ∫_G ∫_{O'} µ(ω') conj((E_{P'}^G ψ'_{ω'})(g)) dω' f_ψ(g) dg`. D'après le Lemme
  VI.2.2, l'intégrale double est absolument convergente. On obtient
  `(f_{ψ'}, f_ψ)_G = ∫_{O'} µ(ω')(E_{P'}^G ψ'_{ω'}, f_ψ)_G dω'`, d'où, d'après le Lemme
  VII.1.1(ii), `(f_{ψ'}, f_ψ)_G = ∫_{O'} µ(ω')(ψ'_{ω'}, f̂_ψ(ω', P')) dω'`. (1)"

  In the printed first identity the coefficient `(E_{P'}^G ψ'_{ω'})(g)` carries an overline
  (complex conjugation), written `conj(…)` here, in accordance with the convention
  `(f₁, f₂)_G = ∫_G conj(f₁(g)) f₂(g) dg` of VII.1 (printed p. 313).

The abstract results this module instantiates are described in `InducedFourierCoherence.md` and
`InducedOrbitWavePacketPairing.md`. In the Library's formula (1):
- the second argument `f_ψ` is replaced by an arbitrary `f ∈ C(G)`, as in the derivation above,
  which uses only `f_ψ ∈ C(G)`;
- a weight `w` stands for `µ`, and its complex conjugate appears because `( , )_G` is
  conjugate-linear in the first argument (`µ` is real);
- `f̂(ω, P)` enters through a smooth section `r` equal to `ψ_f[O, P]` (`hrf`), since the
  statement that `ψ_f[O, P]` is smooth (Proposition VII.1.3) is not assumed.

This module adds no new analysis; it supplies the actual data of `P_I(F)`.

## Setting

The setting combines those of Units 20 and 22:

- `F`, `G`, `hG`, `i`, `hi`, `ν`, `hν`, `I`, and `P = P_I(F)`, as there.
- `K` is open with `hKc` (compact) and `hPK : IsIwasawaPair P₀(F) K`.
- `ρ` is a closed matrix representation (`hρ`) with `ρ(K) ⊆ GL_N(𝒪)` (`hKρ`), so that
  `C(G) = RationalSchwartzSpace hKc hPK ρ`.
- `hM` is the Levi Iwasawa decomposition, which defines `Ξ^{M_I}`.
- `π` is an irreducible admissible representation of `M_I(F)` (the subtype `𝐌`), square
  integrable modulo a central `C` (`hsq`), for an inverse-invariant Haar measure `μM` on
  `M_I(F)/C`.
- `hTA : ∀ A, IsRationalLeviTempered hKc ρ hM A.val.obj`: every representative `A` of the orbit
  `O` of `π` is tempered.
- `μG` is a left and right invariant measure on `G(F)`, and
  `hsw : SquareIntegrableWeight μG Ξ σ` is the conclusion of Lemma II.1.5.
- For the coherence result, in addition, `μG` is inverse-invariant.
- For formula (1), in addition:
  - `μG` is inverse-invariant and s-finite;
  - `[Finite S]` for the stabilizer `S`;
  - `ρX` is a finite measure on `Im X(M_I)`;
  - `w : O → ℂ` is a bounded (`hwb`), almost everywhere strongly measurable (`hwm`) weight;
  - `hcoeff` is the coefficient bound on `π` by `Ξ^{M_I}`.

## Contents

- **`rationalFourierOrbitSection … f`** (definition, the recorded declaration). It is
  `ψ_f[O, P]`, the Library's `fourierOrbitSection` with the actual data. The square
  integrability of every representative comes from `unitaryOrbitRepresentative_isDiscreteSeries`,
  and the tempered growth of every `I_P^G A` from
  `rationalHasTemperedCoefficients_normalizedInduction` (Lemma III.2.3) and `hTA A`.
- **`rationalFourierOrbitSection_apply f A`**: `ψ_f[O, P]_A = f̂(A, P)`, the
  `rationalInducedFourierTransform` of Unit 22 at the representative `A`.
- **`rationalFourierOrbitSection_mem_coherent f`**: for inverse-invariant `μG`
  (`[μG.IsInvInvariant]`), `ψ_f[O, P]` is coherent: its values at two representatives of one
  class correspond under every equivalence between them.
- **`pairing_rationalInducedOrbitWavePacket_eq_integral_productPairing … q r f hrf`** (formula
  (1)). Suppose `r ∈ C^∞(O, P)` satisfies `r = ψ_f[O, P]`. Then
  `(f_ψ, f)_G = ∫_O conj(w(ω)) (ψ_ω, f̂(ω, P)) dω`. Here:
  - `f_ψ = rationalInducedOrbitWavePacket … q` is the wave packet of `q` (Unit 20);
  - `(φ₁, φ₂)_G = ∫ conj(φ₁) φ₂ dμG` (`pairing`);
  - `(ψ_ω, f̂(ω, P))` is the product of V.2 (`unitaryOrbitProductPairing … q r ω`);
  - the measure on `O` is `discreteSeriesOrbitMeasure` for `ρX`.

## Proofs

- `rationalFourierOrbitSection_apply` and `_mem_coherent` apply `fourierOrbitSection_apply` and
  `fourierOrbitSection_mem_coherent` with the actual data, after unfolding the definitions.
  (A direct `rfl` for `_apply` exceeds the heartbeat limit.)
- Formula (1) applies `pairing_inducedOrbitWavePacket_eq_integral_productPairing` with:
  - the data of Unit 20;
  - the Laurent property and continuity of `leviRationalUnitaryCoordinates`;
  - `isUnimodularModulus_standardUnipotentPoints`, `rationalLeviData`, `hM`,
    `rationalMinimalModulus_eq_one`;
  - the data of Unit 22 for the Fourier side.

  It then unfolds `unitaryOrbitWeightedProductPairing` and `rationalInducedOrbitWavePacket`.
  The final step is `with_reducible_and_instances exact`, as in Units 19–22.

## Scope and hypotheses

- Only standard parabolics `P_I ⊇ P₀` are covered.
- `hsw` (Lemma II.1.5) and `hTA` are hypotheses, as in Unit 22. For square-integrable
  representatives `hTA` follows from Corollary III.1.2 (`RationalSquareIntegrableRapidDecayStatement`,
  unproved). `hcoeff` is the same hypothesis as in Unit 20.
- Proposition VII.1.3 (`ψ_f[O, P] ∈ C^∞(O, P)`) is not proved on actual points. Formula (1)
  takes the smooth section `r` with `r = ψ_f[O, P]` as data.
- The rest of the proof of Proposition VII.2.2 (vanishing for non-conjugate Levi subgroups,
  the intertwining operators and `γ(G|M) c(G|M)²`) is not treated here.
- `K`, `hPK`, `hM`, `ρ`, `hρ`, `hKρ` are data (ledger rows S3, S4, S5).
