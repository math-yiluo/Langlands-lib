# Proposition VII.1.3 on actual points: `ψ_f[O, P] ∈ C^∞(O, P)`

Author: Worker 3642, task `1ef6854b-f0e9-4d96-bbe5-cb8c4b52f927` (revision 1).

Lean module: `Langlands.HarmonicAnalysis.HarishChandraSchwartz.RationalFourierOrbitSmoothness`,
namespace `Langlands.HarishChandraSchwartz`. It imports:

- `Langlands.HarmonicAnalysis.HarishChandraSchwartz.RationalInducedOrbitFourierPairing` (this
  author's Unit 23, candidate `ac6c83a8-92f6-4033-b9c5-d54a8c574786`, staged). It provides:
  - `rationalFourierOrbitSection` (`ψ_f[O, P]`);
  - formula (1), `pairing_rationalInducedOrbitWavePacket_eq_integral_productPairing`.

  Through its imports come:
  - Unit 20: `rationalInducedOrbitWavePacket`, `rationalInducedSmoothOrbitSections`,
    `leviRationalUnitaryCoordinates` with `_hasLaurent`, and
    `isConnectedReductive_leviScheme_rootSet`;
  - Unit 22: `compactOpenCofinal_standardLevi`;
  - the published units: `rationalL2Weights`, `rationalXi_inv`, `rationalHeight_inv`,
    `rationalTranslationWeights`, `rationalHasTemperedCoefficients_normalizedInduction`,
    `IsRationalLeviTempered`, `rationalLeviXi`, `compactSpace_subgroupOf_standardLevi`,
    `standardUnipotentModulus`, `isUnimodularModulus_standardUnipotentPoints`.
- `Langlands.HarmonicAnalysis.HarishChandraSchwartz.RationalLeviScheme` (Unit 18, published). It
  provides:
  - `rationalXi_leviScheme` (`Ξ` of the Levi scheme is `Ξ^{M_J}`) and `leviSchemePointsEquiv`;
  - `leviScheme_isAffineHom` and `leviScheme_locallyOfFiniteType`;
  - `isGenericCocharacter_leviTorusHom`;
  - `isOpen_leviSchemeCompact`, `isCompact_leviSchemeCompact`,
    `isIwasawaPair_leviSchemeCompact`.

  Through its imports come:
  - Unit 16: `rationalConstantTermData`, `rationalIsConjModulus`,
    `standardLeviMinimalModulusOf_eq_one`, `rationalLeviXi_pos`;
  - the Library's `standardLevi_isConnectedReductive` and
    `Standard.isMaximalSplitTorus_leviTorusHom`.
- `Langlands.HarmonicAnalysis.HarishChandraSchwartz.FourierOrbitLaurentSmoothness` (Worker 249).
  It provides `fourierOrbitLaurentSmoothSectionLinear`. Through its imports come:
  - `laurentExponent` with `laurentExponent_eq_of_forall`;
  - `xi_uniformTranslationBound`, `heightTranslationBound_of_le_add`;
  - `TranslationWeights`, `L2Weights`, `ConstantTermEstimate`;
  - `rationalValuationCoordinates` and `rationalUnitaryUnramifiedCharacter_apply`.

## Source

J.-L. Waldspurger, *La formule de Plancherel pour les groupes p-adiques, d'après Harish-Chandra*,
J. Inst. Math. Jussieu 2 (2003), 235–333, DOI 10.1017/S1474748003000082 (literature id
`waldspurger-2003-plancherel`, SHA256
`4b6a6162cd0b3863703fb2f65d1698f926caf813114917f2084c16e38f2e30f7`). Page numbers are printed
pages; the PDF page is the printed page minus 234. The author checked the quotations below on the
text of PDF pages 82 and 85.

- Proposition VII.1.3, printed p. 316: "Pour tout `f ∈ C(G)`, la fonction `ψ_f[O, P]` appartient
  à `C^∞(O, P)`. L'application `C(G) → C^∞(O, P)`, `f ↦ ψ_f[O, P]` est continue."
- Lemmas II.1.2 and II.1.4 (printed pp. 251–252) for the Levi subgroup `M`: Waldspurger applies
  Chapter II to every Levi subgroup.
- Formula (1) of the proof of Proposition VII.2.2, printed p. 319, quoted in
  `RationalInducedOrbitFourierPairing.md`.

`FourierOrbitLaurentSmoothness.md` explains how the Library's abstract
`fourierOrbitLaurentSmoothSectionLinear` relates to Proposition VII.1.3. It gives the first
assertion and the map `f ↦ ψ_f[O, P]` as a linear map, without its continuity, in the torus
coordinates of `Im X(M)`.

## Setting

The setting of Units 22 and 23:
- `G`, `i`, `ν`, `I`, `P = P_I(F)`;
- `K` with `hKc` and `hPK`;
- `ρ` with `hρ` and `hKρ`;
- `hM`;
- `π` on `M_I(F)` (the subtype `𝐌`), with `C`, `hC`, `μM`, `hsq`;
- `hTA` (temperedness of every representative of the orbit);
- `μG` with `hsw` (Lemma II.1.5).

`𝐉` is local notation for `rootSet i ν I`. In addition, as `variable`s:

- `μG` is inverse-invariant and σ-finite, normalized by `hμK : μG(K) = 1`.
- `μL` is a left and right invariant, inverse-invariant, s-finite measure on `M_I(F)` (with
  `[MeasurableInv 𝐌]`), normalized by `hMK : μL(K ∩ M_I(F)) = 1`. `hswM` is Lemma II.1.5 for
  `M_I` and `μL`: `∫ Ξ^{M_I}(m)² (1 + σ(m))^{-d} dμL < ∞` for some `d`.
- `hTπ : IsRationalLeviTempered hKc ρ hM π.obj`: `π` itself is tempered.
- `νU` is a Haar measure on `U_I(F)`, right invariant and s-finite, normalized by
  `hUK : νU(K ∩ U_I(F)) = 1`.
- `hE : ConstantTermEstimate νU δ_{U_I} Ξ σ Ξ^{M_I} σ|_{M_I}`. This is the conclusion of the
  published, unproved `RationalConstantTermEstimateStatement` (Proposition II.4.5).
- `hPKiw`: `m u ∈ K ↔ m ∈ K ∧ u ∈ K` for `m ∈ M_I(F)`, `u ∈ U_I(F)`. This is
  `K ∩ P = (K ∩ M)(K ∩ U)`, Renard V.5.1 (3), ledger row S5.
- `hnσ`: `‖n_{M_I}(m)‖ ≤ Cn (1 + σ(m))` for `m ∈ M_I(F)`. Here `n_{M_I}(m)` is the lattice
  coordinate vector (`rationalValuationCoordinates`) of the point of the Levi scheme
  corresponding to `m`, which is `H_{M_I}(m)` in a basis of the lattice `H_{M_I}(M_I(F))`.
- `hint`: for every `f ∈ C(G)`, representative `A` and `ψ ∈ L(A, P)`, the function
  `(g, k) ↦ conj(⟨ψ(k g, k)⟩) f(g)` is integrable on `G(F) × K`.

## Contents

### Levi-side inputs (section `LeviWeights`)

- **`rationalLeviXi_inv`** (Lemma II.1.4 for `M_J`): `Ξ^{M_J}(m⁻¹) = Ξ^{M_J}(m)` for `J ⊆ Δ`.
  - Write `m = j(x)` with `x` a point of the Levi scheme (`leviSchemePointsEquiv`).
  - `rationalXi_leviScheme` turns both sides into `Ξ` of the Levi scheme at `x⁻¹` and `x`.
  - `rationalXi_inv` (Lemma II.1.4) for the Levi scheme then applies. The Levi scheme is
    connected reductive (`standardLevi_isConnectedReductive`), `leviTorusHom` is a maximal split
    torus (`Standard.isMaximalSplitTorus_leviTorusHom`), `ν` is generic
    (`isGenericCocharacter_leviTorusHom`), and `j⁻¹(K)` is compact open with the Iwasawa
    decomposition.
- **`rationalLeviTranslationWeights`** (Lemma II.1.2 for `M_J`, with `d = 0`): the Library's
  `TranslationWeights` for `Ξ^{M_J}` and `σ|_{M_J}`. It combines:
  - positivity, `rationalLeviXi_pos`;
  - `σ ≥ 0`;
  - the two-sided translation bound from `xi_uniformTranslationBound` on `M_J(F)`, since
    `δ₀^{M_J} = 1` on `P₀(F) ∩ M_J(F) ∩ K` (`standardLeviMinimalModulusOf_eq_one`);
  - the height bound from subadditivity of `σ` (`heightTranslationBound_of_le_add`).

### Proposition VII.1.3 (section `Smooth`)

- **`laurentExponent_leviRationalUnitaryCoordinates`**: the Laurent exponent of `m ∈ M_I(F)`
  for the circle coordinates `leviRationalUnitaryCoordinates` is `n_{M_I}(m)`, the valuation
  coordinates of the Levi scheme at the corresponding point. The proof uses uniqueness
  (`laurentExponent_eq_of_forall`) and the character formula
  `rationalUnitaryUnramifiedCharacter_apply` of the Levi scheme. The coordinates are those of
  the Levi scheme by definition (`rfl`).
- **`rationalFourierOrbitSmoothSectionLinear …`** (definition, the recorded declaration). This is
  the ℂ-linear map `C(G) → C^∞(O, P)`, `f ↦ ψ_f[O, P]`: the Library's
  `fourierOrbitLaurentSmoothSectionLinear` with the following inputs:
  - the data of Units 20, 22 and 23;
  - `L2Weights` on `M_I` from `rationalLeviXi_pos` and `hswM`;
  - `rationalLeviXi_inv` and `rationalHeight_inv`;
  - the constant-term data `rationalConstantTermData` and `rationalIsConjModulus`, with `hE`;
  - the translation weights of `G` and of `M_I`;
  - the Laurent property of the coordinates;
  - the growth bound of the Laurent exponent, obtained from `hnσ` through
    `laurentExponent_leviRationalUnitaryCoordinates`.
- **`rationalFourierOrbitSmoothSectionLinear_val f`**: the underlying section is
  `rationalFourierOrbitSection f` (Unit 23). So `ψ_f[O, P] ∈ C^∞(O, P)`, the first assertion of
  Proposition VII.1.3.
- **`pairing_rationalInducedOrbitWavePacket_eq_integral_fourier hwm hwb hcoeff q f`**: formula (1)
  of the proof of Proposition VII.2.2, `(f_ψ, f)_G = ∫_O conj(w(ω)) (ψ_ω, f̂(ω, P)) dω`. It is
  Unit 23's theorem with `r = rationalFourierOrbitSmoothSectionLinear … f`, whose hypothesis
  `r = ψ_f[O, P]` is now `rationalFourierOrbitSmoothSectionLinear_val`. The weight and
  coefficient assumptions on `w`, `ρX` and `hcoeff` are those of Unit 23.

## Proofs

- The definition passes the inputs above to `fourierOrbitLaurentSmoothSectionLinear`, with the
  `(G := rationalPoints G)` and `(M := standardLeviPoints …)` instantiation used since Unit 19.
- `Nonempty (CompactOpenSubgroup M_I(F))` comes from `K ∩ M_I(F)`.
- `SquareIntegrableWeight` (exponent in `ℕ`) is converted to the `square` field of `L2Weights`
  (exponent in `ℝ`).
- `_val` holds by unfolding both definitions and `rfl`.
- The pairing corollary is a direct application of Unit 23's theorem.

## Scope and hypotheses

- Only standard parabolics `P_I ⊇ P₀` are covered.
- The continuity of `f ↦ ψ_f[O, P]` (second assertion of Proposition VII.1.3) is not stated.
- Hypotheses, as listed in the setting:
  - analytic inputs whose actual statements are published but unproved: `hsw` and `hswM`
    (Lemma II.1.5 for `G` and `M_I`), `hE` (Proposition II.4.5), and `hTA` and `hTπ`
    (Corollary III.1.2);
  - the structural fact `hPKiw` (ledger row S5);
  - measure normalizations `hμK`, `hMK`, `hUK`;
  - the height bound `hnσ` for `H_{M_I}`, a standard property of `σ` not formalized on actual
    points;
  - the integrability `hint`.
- `K`, `hPK`, `hM`, `ρ`, `hρ`, `hKρ` are data (ledger rows S3, S4, S5).
