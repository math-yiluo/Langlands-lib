# Lemma VII.1.2 on actual points, and functions with vanishing constant term (Waldspurger VII.1, VIII.2)

Author: Worker 3642, task `1ef6854b-f0e9-4d96-bbe5-cb8c4b52f927` (revision 1).

Lean module:
`Langlands.HarmonicAnalysis.HarishChandraSchwartz.RationalInducedConstantTermFourier`,
namespace `Langlands.HarishChandraSchwartz`. It imports:

- `Langlands.HarmonicAnalysis.HarishChandraSchwartz.RationalFourierOrbitSmoothness` (this
  author's Unit 24, candidate `773beb73-c028-4523-a526-95f1451fef23`, published in
  the Library). From it this module uses `rationalLeviXi_inv` and
  `rationalLeviTranslationWeights`. Through its imports come:
  - Unit 23 (candidate `77e5e21c-3be4-47f0-ad86-6f41ee8ee935`, published in the
    Library): `rationalFourierOrbitSection` (`ψ_f[O, P]`) and `rationalFourierOrbitSection_apply`;
  - Unit 22: `rationalInducedFourierTransform` (`f̂(ω, P)`) and `compactOpenCofinal_standardLevi`;
  - Unit 20: `rationalInducedOrbitWavePacket` (`f_ψ`), `rationalInducedSmoothOrbitSections`
    (`C^∞(O, P)`), `leviRationalUnitaryCoordinates` with `_hasLaurent`;
  - the published units and modules: `RationalSchwartzSpace`, `rationalXi`, `rationalL2Weights`,
    `rationalXi_inv`, `rationalHeight_inv`, `rationalHasTemperedCoefficients_normalizedInduction`,
    `IsRationalLeviTempered`, `rationalLeviXi` with `rationalLeviXi_pos`, `rationalLeviData`,
    `rationalMinimalModulus_eq_one`, `isUnimodularModulus_standardUnipotentPoints`,
    `locallyCompactSpace_standardParabolicPoints_rootSet`, and from `RationalConstantTerm` the
    actual constant term `rationalConstantTerm` with `rationalConstantTermData` and
    `rationalIsConjModulus`.
- `Langlands.HarmonicAnalysis.HarishChandraSchwartz.InducedCoefficientConvergence` (Library):
  `integrable_coefficientPairingIntegrand`. Through its imports come the Library's
  `InducedConstantTermFourier` (`constantTermInducedFourierTransform`,
  `inducedFourierTransform_eq_constantTermInducedFourierTransform`) and `L2Weights`.
- `Langlands.HarmonicAnalysis.HarishChandraSchwartz.CuspidalWavePacketOrthogonality` (Library):
  `constantTermInducedFourierTransform_eq_zero` and
  `pairing_inducedOrbitWavePacket_eq_zero_of_constantTermInd_eq_zero`.

## Source

J.-L. Waldspurger, *La formule de Plancherel pour les groupes p-adiques, d'après Harish-Chandra*,
J. Inst. Math. Jussieu 2 (2003), 235–333, DOI 10.1017/S1474748003000082 (literature id
`waldspurger-2003-plancherel`, SHA256
`4b6a6162cd0b3863703fb2f65d1698f926caf813114917f2084c16e38f2e30f7`). Page numbers are printed
pages; the PDF page is the printed page minus 234. The author checked the quotations below on
the rendered images of PDF pages 38, 81, 87 and 88. Overlines in the source (complex conjugation)
are written `\overline{…}`.

- III.6, printed p. 272: "On définit un homomorphisme `G × G` équivariant
  `C(G) → I_{P×P}^{G×G} C(M)`, `f ↦ f^{(P),Ind}` par
  `f^{(P),Ind}(g_1, g_2) = (ρ(g_1)λ(g_2)f)^{(P)}` pour tous `g_1, g_2 ∈ G`."
- VII.1, printed p. 315, before Lemma VII.1.2: "Pour `f ∈ C(G)`, on a défini `f^{(P)} ∈ C(M)` en
  III.6. On peut donc définir `f̂^{(P)}(ω, M) ∈ L_M(ω, M) = E ⊗ Ě`. On déduit de cette
  construction un élément noté `f̂^{(P),Ind}(ω) ∈ Ind_{P×P}^{G×G}(E ⊗ Ě) = L(ω, P)`, défini par
  `f̂^{(P),Ind}(ω)(g_1, g_2) = [f^{(P),Ind}(g_1, g_2)]^(ω, M)` pour tous `g_1, g_2 ∈ G`."
- Lemma VII.1.2, printed p. 315: "Pour tout `f ∈ C(G)`, on a l'égalité
  `f̂(ω, P) = f̂^{(P),Ind}(ω)`."
- Its proof, printed p. 315, after writing `(v ⊗ v̌, f̂(ω, P))` as
  `∫_G ∫_{P\G} \overline{⟨v(hg), v̌(h)⟩} f(g) dh dg`: "Il résulte de la preuve du Lemme VI.2.2 et
  du Lemme II.1.5 que cette dernière intégrale est absolument convergente."
- Proof of Lemma VIII.2.1, printed p. 321: "Si `f` vérifie cette dernière condition, on a
  `ψ_f[O, P] = 0` pour tout `(O, P) ∈ Θ` tel que `P ≠ G`, d'après le Lemme VII.1.2." The
  condition is that of the lemma: "`f^{(P),Ind} = 0` pour tout sous-groupe parabolique
  semi-standard propre `P` de `G`."
- Proof of Lemma VIII.2.3, printed p. 322: "Soit `g ∈ G`, notons `f'_1` la fonction définie par
  `f'_1(h) = \overline{f_1(gh^{−1})}`. On a l'égalité `(f_1 ∗ f_ψ)(g) = (f'_1, f_ψ)_G`. On montre
  comme en VII.2 (1) que `(f'_1, f_ψ)_G = ∫_O µ(ω)(\hat{f'_1}(ω, P), ψ_ω) dω`. Mais
  `f'_1 ∈ °C(G)` d'après le Lemme VIII.2.1, donc `\hat{f'_1}(ω, P) = 0` pour tout `ω`."

`InducedConstantTermFourier.md`, `InducedCoefficientConvergence.md` and
`CuspidalWavePacketOrthogonality.md` (Library) explain how the abstract results relate to these
statements. This module adds no new analysis: it supplies the actual data of `P_I(F)`.

Correspondence:

- `rationalConstantTermInducedFourierTransform … f` is `f̂^{(P),Ind}(ω)` for `ω = A` and the
  actual standard parabolic `P = P_I(F)`. Its value at `(g₁, g₂)`
  (`eval_rationalConstantTermInducedFourierTransform`) is the Fourier transform at `ω` of
  `rationalConstantTerm … (Space.translate … g₁ g₂ f)`, where `Space.translate … g₁ g₂ f` is
  `ρ(g₁) λ(g₂) f : x ↦ f(g₂⁻¹ x g₁)` and `rationalConstantTerm` is the actual constant term
  `f ↦ f^{(P)}`, `f^{(P)}(m) = δ_{U_I}(m)^{1/2} ∫_{U_I(F)} f(m u) du` (III.6). The Fourier
  transform `φ ↦ φ^(ω, M)` of `C(M_I)` is the Library's `coefficientFourierTransform` with the
  formal degree `d(ω)` of `ω`.
- `integrable_rationalCoefficientPairingIntegrand` is the absolute convergence quoted from the
  proof of Lemma VII.1.2. The source integrates over `G × P\G`; the Lean integral is over
  `G(F) × K`, with `ψ(k g, k)` for `ψ ∈ L(A, P)` in place of `v(hg) ⊗ v̌(h)` (the Library's
  `CompactInduction.integrand`). The two inputs named by the source enter as hypotheses: the
  coefficient bound of Corollary III.1.2 for `M_I` (`hcoeff`, which the proof of Lemma VI.2.2
  uses) and the conclusion of Lemma II.1.5 for `G` (`hsw`).
- `rationalInducedFourierTransform_eq_rationalConstantTermInducedFourierTransform` is Lemma VII.1.2
  for `P = P_I(F)`. This discharges the hypothesis `hint` of Unit 24
  (`rationalFourierOrbitSmoothSectionLinear`) and Unit 25: given `hcoeff`, `hint` holds for every
  `ψ`.
- The vanishing results take `h0 : ∀ g₁ g₂, (ρ(g₁) λ(g₂) f)^{(P)} = 0`, that is
  `f^{(P),Ind} = 0`, for the one parabolic `P = P_I(F)`. Lemma VIII.2.1 asks it for every proper
  semi-standard `P`.
  - `rationalInducedFourierTransform_eq_zero_of_rationalConstantTerm_eq_zero` gives
    `f̂(ω, P) = 0` (by Lemma VII.1.2).
  - `rationalFourierOrbitSection_eq_zero_of_rationalConstantTerm_eq_zero` gives
    `ψ_f[O, P] = 0` for the orbit `O` of `π`: the first sentence of the proof of Lemma VIII.2.1,
    for one pair `(O, P)`.
  - `pairing_rationalInducedOrbitWavePacket_eq_zero_of_rationalConstantTerm_eq_zero` gives
    `(f_ψ, f)_G = 0` for the wave packet `f_ψ` of every `ψ ∈ C^∞(O, P)`: the vanishing
    `(f'_1, f_ψ)_G = 0` in the proof of Lemma VIII.2.3, stated for a function `f` that satisfies
    `h0` in place of `f'_1`, and with the order of the arguments exchanged (the two pairings are
    complex conjugate). The wave packet has a weight `w` on the orbit in place of `µ(ω)`, as in
    Unit 20.
- Not formalized here: `°C(G)`, the other direction of Lemma VIII.2.1 (which uses Theorem
  VII.2.5), the fact that `f'_1` satisfies `h0` when `f_1` does, the identity
  `(f_1 ∗ f_ψ)(g) = (f'_1, f_ψ)_G`, and Lemma VIII.2.3 itself.

## Setting

As in Unit 22, `RationalInducedFourierTransform.md`, and Unit 24,
`RationalFourierOrbitSmoothness.md`:

- `G` connected reductive over a nonarchimedean local field `F` (`hG`), with a maximal split torus
  `i` (`hi`), a generic cocharacter `ν` (`hν`) and `I` a finite set of simple roots; `P = P_I(F)`
  with Levi factor `M_I(F)` (the subtype `𝐌`) and unipotent radical `U_I(F)`; `𝐉` is local
  notation for `rootSet i ν I`;
- `K` an open subgroup with `hKc : IsCompact K` and `hPK : IsIwasawaPair P₀(F) K`;
- a matrix representation `ρ : MatrixRepresentation G (Fin N)` defining `σ = rationalHeight ρ`,
  so that `C(G) = RationalSchwartzSpace hKc hPK ρ` (the Library's `Space Ξ σ` for
  `Ξ = rationalXi hKc hPK`);
- `hM : IsIwasawaPair (P₀(F) ∩ M_I(F)) (K ∩ M_I(F))`, which defines `Ξ^{M_I} = rationalLeviXi`.

`integrable_rationalCoefficientPairingIntegrand` takes in addition a smooth representation `A` of
`M_I(F)`, `hcoeff : ∀ v ℓ, ∃ c > 0, ∀ m, ‖ℓ(A(m) v)‖ ≤ c Ξ^{M_I}(m)` (Corollary III.1.2 for
`A`), an s-finite measure `μG` on `G(F)` with `hsw : SquareIntegrableWeight μG Ξ σ` (Lemma II.1.5
for `G`), `ψ ∈ L(A, P)` (`productInducedCoefficientObject …`) and `f ∈ C(G)`.
`rationalLeviL2Weights` takes a measure `μL` on `M_I(F)` and
`hswM : SquareIntegrableWeight μL Ξ^{M_I} σ` (Lemma II.1.5 for `M_I`).

Section `Representative` (the definition and Lemma VII.1.2):

- `hρ : IsClosedSubgroup ρ` and `hKρ : K ≤ rationalHeightSubgroup ρ`;
- a smooth representation `A` of `M_I(F)` with a normal subgroup `C` of the centre (`hC`), a Haar
  measure `μM` on `M_I(F)/C` (inverse-invariant), `hsq` (square integrable modulo `C`), `hirr`
  (irreducible) and `hTA : IsRationalLeviTempered hKc ρ hM A`;
- `μL` (left and right invariant) with `hswM`;
- a Haar measure `νU` on `U_I(F)`, right invariant, with
  `hE : ConstantTermEstimate νU δ_{U_I} Ξ σ Ξ^{M_I} σ` (the conclusion of Proposition II.4.5).

The definition and `eval_…` use only these. Lemma VII.1.2 and the vanishing theorem take further:
`μG` (left and right invariant, inverse-invariant, σ-finite) with `hsw` and `hμK : μG(K) = 1`;
`[MeasurableInv 𝐌]`, `[μL.IsInvInvariant]`, `[SFinite μL]`, `[SFinite νU]`;
`hPKiw : ∀ m n, m n ∈ K ↔ m ∈ K ∧ n ∈ K` (`P ∩ K = (M_I ∩ K)(U_I ∩ K)`);
`hMK : μL(M_I ∩ K) = 1`, `hUK : νU(U_I ∩ K) = 1`; and `hcoeff` for `A`.

Section `Orbit`: the same data with an irreducible admissible representation `π` of `M_I(F)` in
place of `A` (and `hsq` for `π`), `hTA` for every representative `A` of the unitary unramified
orbit of `π` (`UnitaryOrbitRepresentative (leviRationalNormCharacters i ν I) π`), and
`hcoeffA`: Corollary III.1.2 for every such representative. The pairing theorem takes in
addition `[Finite]` for the stabilizer of the class of `π` in `Im X(M_I)`, a finite measure `ρX`
on `Im X(M_I)`, a weight `w` on the orbit with `hwm` (a.e. strongly measurable for the orbit
measure) and `hwb : ∀ ω, ‖w ω‖ ≤ b`, `hcoeff` for `π`, and a section `q ∈ C^∞(O, P)`.

## Contents

- **`integrable_rationalCoefficientPairingIntegrand … A hcoeff hsw ψ f`**:
  `(g, k) ↦ conj(CompactInduction.integrand … A K g ψ k) * f(g)`, that is
  `conj⟨ψ(k g, k)⟩ f(g)`, is integrable on `G(F) × K` for `μG × CompactInduction.measure K hKc`
  (the Haar probability measure on `K`).
- **`rationalLeviL2Weights … hswM`**: `L2Weights μL Ξ^{M_I} σ`, that is `Ξ^{M_I} > 0`,
  `σ ≥ 0` and `hswM`.
- **`rationalConstantTermInducedFourierTransform … A C hC μM hsq hirr hTA hswM νU hE f`**
  (definition, the recorded declaration): `f̂^{(P),Ind}(ω) ∈ L(A, P)`, the Library's
  `constantTermInducedFourierTransform` on the actual data of `P_I(F)`.
- **`eval_rationalConstantTermInducedFourierTransform … f g₁ g₂`**: its value at `(g₁, g₂)` is
  `coefficientFourierTransform A … d(ω) (rationalConstantTerm … (Space.translate … g₁ g₂ f))`,
  with `d(ω) = representationFormalDegree C hC μM … hsq hirr` (by `rfl`).
- **`rationalInducedFourierTransform_eq_rationalConstantTermInducedFourierTransform … hcoeff f`**
  (Lemma VII.1.2): `rationalInducedFourierTransform … A … hsw f =
  rationalConstantTermInducedFourierTransform … A … f`.
- **`rationalInducedFourierTransform_eq_zero_of_rationalConstantTerm_eq_zero … hcoeff f h0`**:
  `rationalInducedFourierTransform … A … hsw f = 0`.
- **`rationalFourierOrbitSection_eq_zero_of_rationalConstantTerm_eq_zero … f h0`**:
  `rationalFourierOrbitSection … π … hsw f = 0`.
- **`pairing_rationalInducedOrbitWavePacket_eq_zero_of_rationalConstantTerm_eq_zero … hwm hwb
  hcoeff q f h0`**: `pairing μG (rationalInducedOrbitWavePacket … π … ρX w q) f = 0`, where
  `pairing μG φ₁ φ₂ = ∫ conj(φ₁) φ₂ dμG`.

## Proofs

Each result applies the corresponding Library lemma to the actual data of `P_I(F)` (as in Units
20–25): the semidirect decomposition `isSemidirectDecomposition_standard`, closedness of
`U_I(F)` and `P_I(F)`, the factorization `G = P K` (`exists_standardParabolicPoints_rootSet_mul`),
unimodularity of `G(F)` and `U_I(F)`, the modulus of `P_I(F)`, `compactOpenCofinal_standardLevi`,
`rationalL2Weights`, `rationalXi_inv`, `rationalHeight_inv`, `rationalLeviXi_inv`, the
constant-term data `rationalConstantTermData` and `rationalIsConjModulus`, and the translation
weights. The goal is then unfolded to the Library's definitions and closed by
`with_reducible_and_instances exact`.

- `integrable_rationalCoefficientPairingIntegrand`: `integrable_coefficientPairingIntegrand` with
  `rationalLeviData`, `hPK`, `hM`, `rationalMinimalModulus_eq_one`, `hcoeff` and
  `rationalL2Weights … hsw`.
- `rationalLeviL2Weights`: `rationalLeviXi_pos`, `rationalHeight_nonneg` and `hswM`.
- The definition is `constantTermInducedFourierTransform` with `rationalLeviL2Weights`,
  `hsq.1`, `hTA` and the formal degree; `eval_…` holds by `rfl`.
- Lemma VII.1.2: `inducedFourierTransform_eq_constantTermInducedFourierTransform`, with
  temperedness of the induced representation from
  `rationalHasTemperedCoefficients_normalizedInduction`, the normalizations and `hPKiw`, and its
  integrability hypothesis supplied by `integrable_rationalCoefficientPairingIntegrand … hcoeff hsw`.
- `f̂(ω, P) = 0`: `constantTermInducedFourierTransform_eq_zero` (with `fun x => h0 x.1 x.2`)
  gives `f̂^{(P),Ind}(ω) = 0`; combine with Lemma VII.1.2.
- `ψ_f[O, P] = 0`: function extensionality over the representatives `A`, rewrite with
  `rationalFourierOrbitSection_apply`, and apply the previous result to `A.val.obj` with
  `unitaryOrbitRepresentative_isDiscreteSeries`, `A.val.property.1` (irreducibility), `hTA A` and
  `hcoeffA A`.
- `(f_ψ, f)_G = 0`: `pairing_inducedOrbitWavePacket_eq_zero_of_constantTermInd_eq_zero` with the
  data of Unit 20 (norm characters, circle coordinates with their Laurent property and
  continuity), the constant-term data, the integrability for each representative from
  `integrable_rationalCoefficientPairingIntegrand … (hcoeffA A) hsw`, and
  `fun x => h0 x.1 x.2`.

## Scope and hypotheses

- Only standard parabolics `P_I ⊇ P₀` are covered, and the vanishing results concern one
  parabolic and one orbit.
- Analytic inputs whose actual statements are published but unproved enter as hypotheses: `hsw`
  and `hswM` (Lemma II.1.5 for `G` and `M_I`), `hE` (Proposition II.4.5), `hTA` (temperedness),
  `hcoeff` and `hcoeffA` (Corollary III.1.2 for `ω`, for `π` and for each representative of its
  orbit; the bound for the representatives is not derived from the bound for `π`).
- The structural fact `hPKiw` (ledger row S5) and the measure normalizations `hμK`, `hMK`, `hUK`
  are hypotheses, as in Lemma VII.1.2 of the Library.
- `K`, `hPK`, `hM`, `ρ`, `hρ`, `hKρ` are data (ledger rows S3, S4, S5).
- The Plancherel density `µ` (V.2) is not formalized; the wave packet uses the weight `w`.
