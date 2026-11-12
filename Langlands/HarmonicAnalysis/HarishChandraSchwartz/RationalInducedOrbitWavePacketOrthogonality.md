# Wave packets detect `ψ_f[O, P]` on actual points (Waldspurger VII.2, proof of Corollary VII.2.3)

Author: Worker 3642, task `1ef6854b-f0e9-4d96-bbe5-cb8c4b52f927` (revision 1).

Lean module:
`Langlands.HarmonicAnalysis.HarishChandraSchwartz.RationalInducedOrbitWavePacketOrthogonality`,
namespace `Langlands.HarishChandraSchwartz`. It imports:

- `Langlands.HarmonicAnalysis.HarishChandraSchwartz.RationalFourierOrbitSmoothness` (this
  author's Unit 24, candidate `773beb73-c028-4523-a526-95f1451fef23`, review-accepted). It
  provides `rationalFourierOrbitSmoothSectionLinear` (Proposition VII.1.3 on actual points) and
  `rationalFourierOrbitSmoothSectionLinear_val`. Through its imports come:
  - Unit 23 (candidate `77e5e21c-3be4-47f0-ad86-6f41ee8ee935`, review-accepted):
    `rationalFourierOrbitSection` (`ψ_f[O, P]`) and `rationalFourierOrbitSection_apply`;
  - Unit 20: `rationalInducedOrbitWavePacket` (`f_ψ`), `rationalInducedSmoothOrbitSections`
    (`C^∞(O, P)`), `leviRationalUnitaryCoordinates` with `_hasLaurent`;
  - Unit 22: `rationalInducedFourierTransform` (`f̂(ω, P)`) and `compactOpenCofinal_standardLevi`;
  - the published units: `RationalSchwartzSpace`, `rationalXi`, `rationalL2Weights`,
    `rationalXi_inv`, `rationalHeight_inv`, `rationalHasTemperedCoefficients_normalizedInduction`,
    `IsRationalLeviTempered`, `rationalLeviXi`, `rationalLeviData`,
    `rationalMinimalModulus_eq_one`, `isUnimodularModulus_standardUnipotentPoints`,
    `locallyCompactSpace_standardParabolicPoints_rootSet`.
- `Langlands.HarmonicAnalysis.HarishChandraSchwartz.InducedOrbitWavePacketOrthogonality`
  (Library). It provides `unitaryOrbitWeightedProductCore` and
  `fourierOrbitSection_eq_zero_iff_forall_pairing_inducedOrbitWavePacket_eq_zero`. Through its
  imports come `unitaryOrbitProductPairing`, `discreteSeriesOrbitMeasure`,
  `inducedOrbitWavePacket`, `pairing` and `unitaryOrbitRepresentative_isDiscreteSeries`.

## Source

J.-L. Waldspurger, *La formule de Plancherel pour les groupes p-adiques, d'après Harish-Chandra*,
J. Inst. Math. Jussieu 2 (2003), 235–333, DOI 10.1017/S1474748003000082 (literature id
`waldspurger-2003-plancherel`, SHA256
`4b6a6162cd0b3863703fb2f65d1698f926caf813114917f2084c16e38f2e30f7`). Page numbers are printed
pages; the PDF page is the printed page minus 234. The author checked the quotations below on
the rendered image of PDF page 85. The three displays quoted carry no overline in the printed
text.

- Corollary VII.2.3, printed p. 319: "Soient `P = MU`, `P' = M'U'` deux sous-groupes
  paraboliques semi-standards de `G`, `O ⊂ ℰ_2(M)` une orbite pour l'action de `Im X(M)`,
  `ω' ∈ ℰ_2(M')` et `ψ ∈ C^∞(O; P)`. Supposons `M'` non conjugué à `M`. Alors
  `f̂_ψ(ω', P') = 0`."
- Its proof, printed p. 319: "Notons `O'` l'orbite de `ω'` pour l'action de `Im X(M')`. Soit
  `ψ' ∈ C^∞(O'; P')`. D'après le (i) de la proposition précédente et la formule (1) de sa preuve
  on a l'égalité `∫_{O'} µ(ω'')(ψ'_{ω''}, f̂_ψ(ω'', P')) dω'' = 0`. Cette égalité valant pour
  tout `ψ'`, elle entraîne `f̂_ψ(ω'', P') = 0` pour tout `ω'' ∈ O'`."
- Formula (1) of the proof of Proposition VII.2.2, printed p. 319:
  `(f_{ψ'}, f_ψ)_G = ∫_{O'} µ(ω')(ψ'_{ω'}, f̂_ψ(ω', P')) dω'`.
- VII.2, printed p. 319, after Corollary VII.2.3: "Pour `ψ, ψ' ∈ C^∞(Θ)^inv`, posons
  `(ψ', ψ) = Σ_{(O, P = MU) ∈ Θ} c(G|M)^{-2} γ(G|M)^{-1} |W^M| |W^G|^{-1} |𝒫(M)|^{-1}
  × ∫_O µ(ω)(ψ'[O, P]_ω, ψ[O, P]_ω) dω`. Cela définit un produit hermitien défini positif
  invariant par `G × G` sur `C^∞(Θ)^inv`."

`InducedOrbitWavePacketOrthogonality.md` explains how the Library's abstract results relate to
these statements. This module adds no new analysis: it supplies the actual data of `P_I(F)` and
the smoothness of `ψ_f[O, P]` from Unit 24.

Correspondence:

- The source's last step is implicit. The Lean proof (in the Library) takes `ψ'` to be the
  section `ψ_f[O, P]` itself. That section lies in `C^∞(O, P)` by Proposition VII.1.3, here
  Unit 24's `rationalFourierOrbitSmoothSectionLinear`. Formula (1) then gives
  `∫_O u(ω) (ψ_f[O, P]_ω, ψ_f[O, P]_ω) dω = 0`, and the definiteness of the weighted product
  gives `ψ_f[O, P] = 0`.
- Roles: the source's orbit `O'`, parabolic `P'`, test section `ψ'` and function `f_ψ` are here:
  - the orbit `O` of the class of `π`, a representation of `M_I(F)`;
  - the actual standard parabolic `P = P_I(F)`;
  - the section `q ∈ C^∞(O, P)`;
  - an arbitrary `f ∈ C(G)`.
- The source's hypothesis is the vanishing of `∫_{O'} µ(ω'')(ψ'_{ω''}, f̂_ψ(ω'', P')) dω''` for
  every `ψ'`. Through formula (1) it enters as `(f_{ψ'}, f)_G = 0` for every wave packet `f_{ψ'}`
  (hypothesis `h0`, or the right side of the equivalence). The source derives this vanishing
  from Proposition VII.2.2 (i), which this module does not prove.
- The conclusion "`f̂_ψ(ω'', P') = 0` pour tout `ω'' ∈ O'`" is stated at each representative `A`
  of each class of `O` (`f̂(A, P) = rationalInducedFourierTransform … A.val.obj … f`).
- The weight `u` is a real, bounded, continuous, strictly positive function on the orbit in place
  of the Plancherel density `µ` of V.2, which is not formalized. The measure on the orbit is the
  orbit measure of a finite measure `ρX` on `Im X(M_I)` that is positive on nonempty open sets.
- `rationalUnitaryOrbitWeightedProductCore` is the summand of the VII.2 product for one pair
  `(O, P)`, with `u` in place of `µ`. Its positive definiteness is the content of "Cela définit un
  produit hermitien défini positif" restricted to one orbit. Not treated: the constants
  `c(G|M)^{-2} γ(G|M)^{-1} |W^M| |W^G|^{-1} |𝒫(M)|^{-1}`, the sum over `Θ`, the restriction to
  `C^∞(Θ)^inv` and the `G × G` invariance.
- Derived results, not statements of the paper: `rationalUnitaryOrbitWeightedProductCore_inner`
  (definitional) and the converse half of the equivalence (vanishing of `ψ_f[O, P]` implies the
  vanishing of every pairing).

## Setting

The setting of Unit 24, `RationalFourierOrbitSmoothness.md`:

- `G`, `i`, `ν`, `I`, `P = P_I(F)`; `K` with `hKc` and `hPK`; `ρ` with `hρ` and `hKρ`, so that
  `C(G) = RationalSchwartzSpace hKc hPK ρ`; `hM`, which defines `Ξ^{M_I}`;
- `π` on `M_I(F)` (the subtype `𝐌`), with `C`, `hC`, an inverse-invariant Haar measure `μM` on
  `M_I(F)/C`, and `hsq`;
- `hTA` (temperedness of every representative of the orbit) and `hTπ` (of `π`);
- `μG` (left and right invariant, inverse-invariant, σ-finite) with `hsw` (Lemma II.1.5) and
  `hμK : μG(K) = 1`;
- `μL` on `M_I(F)` with `hswM` and `hMK`; `νU` on `U_I(F)` with `hUK`;
- `hE` (Proposition II.4.5), `hPKiw` (`K ∩ P = (K ∩ M)(K ∩ U)`), `hnσ`
  (`‖H_{M_I}(m)‖ ≤ Cn (1 + σ(m))` in lattice coordinates) and `hint` (integrability).

`𝐉` is local notation for `rootSet i ν I`. In addition:

- `[Finite S]` for the stabilizer `S = discreteSeriesStabilizer …` of the class of `π` in
  `Im X(M_I)`;
- `[Finite (𝐌 ⧸ (commonNormKernel (leviRationalNormCharacters i ν I) ⊔ C))]`: `M_I(F)` modulo
  the common kernel of its norm characters and `C` is finite (a hypothesis of the Library's
  section);
- `ρX` is a measure on `Im X(M_I)` (`unitaryUnramifiedCharacters`), and
  `u : O → ℝ` is a real weight on the orbit `O = discreteSeriesOrbit C hC μM … (discreteSeriesClass
  C hC μM π hsq)`.

The core and the two theorems also take `[IsFiniteMeasure ρX]`, `[ρX.IsOpenPosMeasure]`,
`hu : Continuous u`, `hupos : ∀ ω, 0 < u ω`, a real `b` and `hub : ∀ ω, u ω ≤ b`. The two
theorems also take:
- `hcoeff : ∀ v ℓ, ∃ c > 0, ∀ m, ‖ℓ(π(m) v)‖ ≤ c Ξ^{M_I}(m)` (the conclusion of Corollary III.1.2
  for `π`, the same hypothesis as in Units 20, 23 and 24);
- `f : RationalSchwartzSpace hKc hPK ρ`.

The core uses only `hG`, `hi`, `hν`, `I`, `hKc`, `hPK`, `π`, `C`, `hC`, `μM`, `hsq`, `ρX`, `u`
and the two finiteness instances; the theorems use, through `include`, all the hypotheses of
Unit 24's `rationalFourierOrbitSmoothSectionLinear`.

## Contents

Write `f_ψ = rationalInducedOrbitWavePacket … ρX (fun ω => (u ω : ℂ)) q` for the actual wave
packet of weight `u` of `q ∈ C^∞(O, P)` (Unit 20), `(φ₁, φ₂)_G = pairing μG φ₁ φ₂ = ∫ conj(φ₁) φ₂ dμG`,
and `(q_ω, r_ω) = unitaryOrbitProductPairing … q r ω`, the product of V.2 on the fibre at `ω`.

- **`rationalUnitaryOrbitWeightedProductCore … ρX u hu hupos hub`** (definition, the recorded
  declaration):
  `InnerProductSpace.Core ℂ (rationalInducedSmoothOrbitSections hG hi hν I hKc hPK π)`, the
  Library's `unitaryOrbitWeightedProductCore` with the actual data of `P_I(F)` and the circle
  coordinates `leviRationalUnitaryCoordinates`. As for every `InnerProductSpace.Core`, it is
  conjugate-linear in the first argument, additive, hermitian, with nonnegative real part on the
  diagonal, and definite.
- **`rationalUnitaryOrbitWeightedProductCore_inner`**: its inner product is
  `⟪q, r⟫ = ∫_O u(ω) (q_ω, r_ω) dω`, the measure being `discreteSeriesOrbitMeasure` for `ρX`.
- **`rationalFourierOrbitSection_eq_zero_iff_forall_pairing_rationalInducedOrbitWavePacket_eq_zero
  … hu hupos hub hcoeff f`**: `rationalFourierOrbitSection … f = 0` (that is, `ψ_f[O, P] = 0`)
  if and only if `(f_ψ, f)_G = 0` for every `q ∈ C^∞(O, P)`.
- **`rationalInducedFourierTransform_eq_zero_of_forall_pairing_rationalInducedOrbitWavePacket_eq_zero
  … hu hupos hub hcoeff f h0 A`**: if `h0 : ∀ q, (f_ψ, f)_G = 0`, then for every representative
  `A : UnitaryOrbitRepresentative (leviRationalNormCharacters i ν I) π` of the orbit,
  `rationalInducedFourierTransform hG hi hν I hKc hPK ρ hρ hKρ hM A.val.obj C hC μM … hsw f = 0`,
  that is `f̂(A, P) = 0`.

## Proofs

- The core is `unitaryOrbitWeightedProductCore` applied to the data of Unit 20 (the semidirect
  decomposition of `P_I(F)`, closedness, `K`, the factorization `G = P K`, unimodularity, the
  modulus of `P_I(F)`, the norm characters and their continuity, the projection, the circle
  coordinates and their continuity, `compactOpenCofinal_standardLevi`), with the local compactness
  of `P_I(F)`. `_inner` holds by `rfl`.
- The equivalence:
  1. `hsm : ψ_f[O, P] ∈ C^∞(O, P)` is the `property` of
     `rationalFourierOrbitSmoothSectionLinear … f`, rewritten with
     `rationalFourierOrbitSmoothSectionLinear_val` (Unit 24).
  2. The Library's `fourierOrbitSection_eq_zero_iff_forall_pairing_inducedOrbitWavePacket_eq_zero`
     is applied with the actual data, as for formula (1) in Unit 23: `rationalL2Weights`,
     temperedness from `rationalHasTemperedCoefficients_normalizedInduction` and `hTA`,
     `rationalXi_inv`, `rationalHeight_inv`, the Laurent property and continuity of the
     coordinates, `isUnimodularModulus_standardUnipotentPoints`, `rationalLeviData`, `hM`,
     `rationalMinimalModulus_eq_one`, `hcoeff`, `f` and `hsm`.
  3. The goal is unfolded (`rationalFourierOrbitSection`, `rationalInducedOrbitWavePacket`, and
     `delta rationalXi`, since the Library's `f` lies in `Space (xi hP₀K δ₀) σ` while
     `RationalSchwartzSpace` is written with `rationalXi`), and closed by
     `with_reducible_and_instances exact`.
- The corollary rewrites `f̂(A, P)` as `ψ_f[O, P]_A` (`rationalFourierOrbitSection_apply`,
  backwards), replaces `ψ_f[O, P]` by `0` using the equivalence and `h0`, and closes by `rfl`.

## Scope and hypotheses

- Only standard parabolics `P_I ⊇ P₀` are covered.
- Corollary VII.2.3 itself is not proved: the vanishing hypothesis `h0` for wave packets on a
  non-conjugate Levi subgroup is Proposition VII.2.2 (i), which is not proved on actual points
  (nor in the Library; see `InducedOrbitWavePacketOrthogonality.md`).
- The Plancherel density `µ` (V.2) is not formalized; `u` stands in for it.
- The hermitian product on `C^∞(Θ)^inv` (the sum over `Θ` with its constants) and its `G × G`
  invariance are not formalized.
- Hypotheses inherited from Unit 24: analytic inputs whose actual statements are published but
  unproved (`hsw` and `hswM`, Lemma II.1.5 for `G` and `M_I`; `hE`, Proposition II.4.5; `hTA`
  and `hTπ`, Corollary III.1.2), the structural fact `hPKiw` (ledger row S5), the measure
  normalizations `hμK`, `hMK`, `hUK`, the height bound `hnσ` and the integrability `hint`.
- `hcoeff` (Corollary III.1.2 for `π`) and the finiteness instances are hypotheses.
- `K`, `hPK`, `hM`, `ρ`, `hρ`, `hKρ` are data (ledger rows S3, S4, S5).
