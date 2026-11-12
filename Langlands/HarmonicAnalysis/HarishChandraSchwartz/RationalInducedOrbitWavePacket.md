# Wave packets for actual standard parabolic subgroups (Waldspurger VI.1–VI.3)

Author: Worker 3642, task `1ef6854b-f0e9-4d96-bbe5-cb8c4b52f927` (revision 1).

Lean module: `Langlands.HarmonicAnalysis.HarishChandraSchwartz.RationalInducedOrbitWavePacket`,
namespace `Langlands.HarishChandraSchwartz`. It imports:

- `Langlands.HarmonicAnalysis.HarishChandraSchwartz.RationalInducedCoefficients` (this author's
  Unit 19, candidate `181a067e-76c8-4bae-b922-0bd659adbf51`): the coefficient map
  `rationalInducedCoefficientMap` (`E_P^G` on actual points) with
  `rationalInducedCoefficientMap_eq_coefficientMap`, and the actual-point facts
  `isClosed_standardParabolicPoints_rootSet`,
  `locallyCompactSpace_standardParabolicPoints_rootSet` and
  `exists_standardParabolicPoints_rootSet_mul`. Through it come the imports of Unit 14
  (`isUnimodularModulus_standardUnipotentPoints`, `modularCharacter_standardParabolicPoints`),
  `RationalXiLevi` (`rationalLeviXi`, `rationalLeviData`, `compactSpace_subgroupOf_standardLevi`)
  and `RationalWeights` (`rationalXi`, `rationalMinimalModulus_eq_one`).
- `Langlands.HarmonicAnalysis.HarishChandraSchwartz.OrbitWavePacket` (Worker 249): the abstract
  results this module instantiates. These are `inducedOrbitWavePacket`,
  `exists_norm_unitaryOrbitCoefficientMap_le_xi`, `exists_norm_inducedOrbitWavePacket_le_xi`,
  `exists_inducedOrbitWavePacket_biInvariant`, `integrable_inducedOrbitWavePacket_integrand`,
  `inducedOrbitWavePacket_smul`, `inducedOrbitWavePacket_add` and
  `inducedOrbitWavePacket_eq_parameterIntegral`. Through it come Worker 200's
  `productInducedSmoothOrbitSections`, `unitaryOrbitCoefficientMap` (with
  `unitaryOrbitCoefficientMap_representative` and `unitaryOrbitRepresentativeCoefficientMap`),
  `UnitaryOrbitRepresentative`, `unitaryOrbitRepresentativeDiscreteSeriesOrbit`, and the orbit
  data `discreteSeriesOrbit`, `discreteSeriesClass`, `discreteSeriesStabilizer`,
  `discreteSeriesOrbitMap` and `discreteSeriesOrbitMeasure`.
- `Langlands.Representation.Aubert.General.RationalLeviCharacterDensity`. Through its imports
  come:
  - the homeomorphism `leviRationalPointHomeomorph` between the rational points of the Levi
    scheme and the literal Levi subgroup;
  - `RationalPointFamily.pointTopology`, `leviRationalNormCharacters` and
    `continuous_leviRationalNormCharacters`;
  - `unramifiedCharactersHomeomorph` and
    `rationalCanonicalUnitaryUnramifiedCharacterCoordinates`.
- `Langlands.Representation.Plancherel.UnitaryUnramifiedSmoothEvaluation`: the predicate
  `HasLaurentUnitaryCoordinates` and
  `rationalCanonicalUnitaryUnramifiedCharacterCoordinates_hasLaurent`.
- `Langlands.BruhatTits.SpecialCompact.LeviApartmentComparison`:
  `standardLevi_isConnectedReductive`.

## Source

J.-L. Waldspurger, *La formule de Plancherel pour les groupes p-adiques, d'après Harish-Chandra*,
J. Inst. Math. Jussieu 2 (2003), 235–333, DOI 10.1017/S1474748003000082 (literature id
`waldspurger-2003-plancherel`, SHA256
`4b6a6162cd0b3863703fb2f65d1698f926caf813114917f2084c16e38f2e30f7`). Page numbers are printed
pages; the PDF page is the printed page minus 234. The author checked the quotations below on the
text of PDF pages 61, 62, 64, 67 and 68.

- VI.1, printed pp. 295–296: "Soient `P = MU` un sous-groupe parabolique semi-standard de `G` et
  `O ∈ E₂(M)` une orbite pour l'action de `Im X(M)`. [...] Soit `ψ` une fonction qui, à un
  élément `(ω, E)` de `O`, associe un élément `ψ_ω ∈ L(ω, P)`. On demande que `ψ_ω` ne dépende
  que de la classe de `ω` [...] Pour tout `χ ∈ Im X(M)`, `L(ω ⊗ χ, P)` s'identifie à
  `L_K(ω, P)` par restriction à `K`. La fonction `ψ` s'identifie à une fonction sur `Im X(M)` à
  valeurs dans `L_K(ω, P)`. Alors `ψ` est `C^∞` si cette dernière fonction l'est. [...] Notons
  `C^∞(O, P)` l'ensemble des applications `ψ` comme ci-dessus qui sont `C^∞`."
- Lemme VI.2.2, printed p. 298: "Soit `ψ ∈ C^∞(O, P)`. Il existe `C > 0` tel que pour tout
  `ω ∈ O` et tout `g ∈ G`, on ait l'inégalité `|(E_P^G ψ_ω)(g)| ⩽ C Ξ(g)`."
- VI.3, printed pp. 301–302: "On a muni `Im X(M)` d'une mesure. On munit `O` d'une mesure telle
  que l'application `Im X(M) → O`, `χ ↦ ω ⊗ χ` préserve localement les mesures. Pour
  `ψ ∈ C^∞(O, P)` définissons une fonction `f_ψ` sur `G` par
  `f_ψ(g) = ∫_O µ(ω) (E_P^G ψ_ω)(g) dω`."

The Library's abstract versions of these objects, and their relation to Waldspurger's
definitions, are described in `OrbitWavePacket.md` and in the Markdown of Worker 200's
`ProductInducedOrbitSections`. This module adds no new mathematics to them. It supplies the
actual data of a standard parabolic `P_I(F)`, and coordinates on `Im X(M_I)`.

## Setting

- `F` is a nonarchimedean local field.
- `G` is a group scheme over `Spec F` with `[IsAffineHom G.X.hom]` and
  `[LocallyOfFiniteType G.X.hom]`, and `hG : IsConnectedReductive G`.
- `i : S → G` is a maximal split torus (`hi`) and `ν` a generic cocharacter (`hν`).
- `I` is a finite set of simple roots. The standard parabolic is
  `P = P_I(F) = M_I(F) ⋉ U_I(F)`, with the published decomposition
  `isSemidirectDecomposition_standard` for `rootSet i ν I`.
- `G(F) = rationalPoints G` carries the local instances of `RationalWeights` and of
  `RationalInducedCoefficients`.
- `K` is an open subgroup of `G(F)`, with `hKc` (`K` is compact) and
  `hPK : IsIwasawaPair P₀(F) K`.
- `M_I(F)` is written in the statements as the subtype
  `{x : rationalPoints G // @Membership.mem (rationalPoints G) (Subgroup (rationalPoints G)) _
  (standardLeviPoints i ν (rootSet i ν I)) x}`, displayed as `𝐌` through a local notation. It is
  the same subgroup as `standardLeviPoints i ν (rootSet i ν I)`. The explicit membership only
  fixes the ambient type to `rationalPoints G`, the one used by the Library lemmas.
- `π` is an irreducible admissible representation of `M_I(F)`
  (`IrreducibleAdmissibleRep ℂ 𝐌`).
- Orbit data, kept general as in `OrbitWavePacket`:
  - a normal subgroup `C` of `M_I(F)` with `hC : C ≤ center M_I(F)`;
  - a Haar measure `mu` on `M_I(F)/C`;
  - `hsq`: `π` is square integrable modulo `C`.

  Then `O` is the unitary unramified twist orbit of the class of `π`:
  `discreteSeriesOrbit C hC mu (leviRationalNormCharacters i ν I) (discreteSeriesClass C hC mu π hsq)`.
  Waldspurger takes `C = A_{M_I}(F)`.
- For the wave packet, two further data:
  - `[Finite S]`, where `S` is the stabilizer of the class of `π` in `Im X(M_I)`. The Library's
    `finite_discreteSeriesStabilizer` gives this whenever `M_I(F)/(M_I(F)¹ C)` is finite.
  - a measure `ρ` on `Im X(M_I)`, and a weight `w : O → ℂ` in place of Waldspurger's `µ`.
- `hM : IsIwasawaPair (P₀(F) ∩ M_I(F)) (K ∩ M_I(F))`, which defines `Ξ^{M_I} = rationalLeviXi
  hKc hM`.
- `hcoeff`, the coefficient bound on `π`:
  `∀ v ℓ, ∃ c > 0, ∀ m, |ℓ(π(m) v)| ≤ c Ξ^{M_I}(m)`.

## Contents

### Transport of unitary unramified characters (section `Transport`)

- `unitaryUnramifiedCharactersHomeomorph e ν`: a multiplicative homeomorphism `e : A ≃ₜ* B`
  induces `Im X_ν(A) ≃ₜ* Im X_{ν ∘ e⁻¹}(B)`, `χ ↦ χ ∘ e⁻¹`. Here `Im X_ν` is
  `unitaryUnramifiedCharacters ν`. This is the unitary analogue of the Library's
  `unramifiedCharactersHomeomorph`.
  - `unitaryUnramifiedCharactersHomeomorph_apply` is its value.
  - The proofs follow the Library's: unitarity and the kernel condition are checked pointwise.
    Continuity comes from continuity of composition (`continuous_comp_left`).
- `hasLaurentUnitaryCoordinates_transport`: if the coordinates `E` of `Im X_ν(A)` have the
  Laurent property, then so do the transported coordinates `(transport)⁻¹ ∘ E` of
  `Im X_{ν ∘ e⁻¹}(B)`. The Laurent property says that evaluation at each point is an integer
  Laurent character of the coordinates (`HasLaurentUnitaryCoordinates`). The proof uses, at
  `b ∈ B`, the Laurent exponent of `e⁻¹(b)`.

### Coordinates on `Im X(M_I)` (section `LeviCoordinates`)

- `isConnectedReductive_leviScheme_rootSet`: the Levi scheme `M_I` is connected reductive. This
  is the Library's `standardLevi_isConnectedReductive`.
- **`leviRationalUnitaryCoordinates hG hi hν I`** (definition). These are circle coordinates
  `Im X(M_I) ≃ₜ* (Fin r → Circle)` on the unitary unramified characters of the literal Levi
  subgroup `M_I(F)`, for the norm family `leviRationalNormCharacters i ν I`. Here `r` is the
  rank `rationalImageRank` of the Levi scheme.
  - Construction: the Library's canonical coordinates
    `rationalCanonicalUnitaryUnramifiedCharacterCoordinates` of the Levi scheme, transported
    along `leviRationalPointHomeomorph`.
  - It is the unitary analogue of the Library's `leviRationalUnramifiedCharacterCoordinates`.
- `leviRationalUnitaryCoordinates_hasLaurent`: these coordinates have the Laurent property. This
  follows from `rationalCanonicalUnitaryUnramifiedCharacterCoordinates_hasLaurent` and the
  transport lemma.

### `C^∞(O, P)`, orbit coefficients and Lemma VI.2.2 (section `WavePacket`)

- **`rationalInducedSmoothOrbitSections hG hi hν I hKc hPK π`** (abbreviation). This is
  Waldspurger's `C^∞(O, P)` for `P = P_I(F)`: the Library's `productInducedSmoothOrbitSections`,
  with the following actual data:
  - the decomposition of `P_I(F)` and the closedness of `U_I(F)` and `P_I(F)`;
  - `K`, and `G(F) = P_I(F) K` in subtype form (`factorization_subtype`);
  - the norm characters `leviRationalNormCharacters i ν I` and their continuity;
  - the continuity of the Levi projection;
  - the coordinates `leviRationalUnitaryCoordinates`.

  An element is a coherent choice of `ψ_A ∈ L(A, P)` for every representative `A` of every class
  of the orbit, whose restriction to `K × K` is a smooth finite family on the torus of
  parameters.
- **`rationalInducedOrbitCoefficientMap … π C hC mu hsq`** (abbreviation). This is the linear map
  `ψ ↦ (ω ↦ E_P^G ψ_ω)`, valued in `O → LocallyConstant G(F) ℂ`. It is the Library's
  `unitaryOrbitCoefficientMap` on the same data.
- **`rationalInducedOrbitCoefficientMap_representative q A`**. At the orbit class of a
  representative `A`, the orbit coefficient of `ψ = q` is
  `rationalInducedCoefficientMap hG hi hν I hKc hPK A A_adm (q_A)`. That is Unit 19's
  `E_P^G` for `A`, applied to `ψ_A`. So `ω ↦ E_P^G ψ_ω` is Waldspurger's `E_P^G` at every
  point of the orbit.
- **`exists_norm_rationalInducedOrbitCoefficientMap_le_rationalXi hcoeff q`** (Lemma VI.2.2 on
  `C^∞(O, P)`). There is `c > 0` with `|(E_P^G ψ_ω)(g)| ≤ c Ξ(g)` for all `ω ∈ O` and
  `g ∈ G(F)`, where `Ξ = rationalXi hKc hPK`.

### The wave packet

- **`rationalInducedOrbitWavePacket hG hi hν I hKc hPK π C hC mu hsq ρ w q`** (definition, the
  recorded declaration). It is the function `G(F) → ℂ`
  `f_ψ(g) = ∫_O w(ω) (E_P^G ψ_ω)(g) dω`.
  - The measure on `O` is `discreteSeriesOrbitMeasure`: `|S|⁻¹` times the push-forward of `ρ`
    along `χ ↦ π ⊗ χ` (`rationalInducedOrbitWavePacket_apply`, by `rfl`).
  - For a left-invariant measure `ρ` (Waldspurger's choice is a Haar measure), the map
    `χ ↦ π ⊗ χ` preserves measures locally. This is the Library's
    `isLocallyMeasurePreserving_discreteSeriesOrbitMap`, described in `OrbitWavePacket.md`.
    It is Waldspurger's condition on the measure of `O`.
- **`exists_norm_rationalInducedOrbitWavePacket_le_rationalXi hw hcoeff q`**: for finite `ρ` and
  `|w| ≤ b`, there is `c > 0` with `|f_ψ(g)| ≤ c Ξ(g)` on `G(F)`.
- `exists_rationalInducedOrbitWavePacket_biInvariant q`: there is a compact open `H ≤ K` with
  `f_ψ(k g l) = f_ψ(g)` for `k, l ∈ H`.
- `integrable_rationalInducedOrbitWavePacket_integrand hwm hw hcoeff q g`: the integrand
  `ω ↦ w(ω) (E_P^G ψ_ω)(g)` is integrable. This needs finite `ρ` and a bounded,
  almost-everywhere strongly measurable `w`. It uses the Laurent property and the continuity of
  `leviRationalUnitaryCoordinates`.
- `rationalInducedOrbitWavePacket_smul`, `rationalInducedOrbitWavePacket_add` and
  **`rationalInducedOrbitWavePacketLinear`**: `ψ ↦ f_ψ` is a ℂ-linear map
  `C^∞(O, P) → (G(F) → ℂ)`, under the hypotheses of the integrability lemma.
- **`rationalInducedOrbitWavePacket_eq_parameterIntegral hwm q g`**:
  `f_ψ(g) = |S|⁻¹ ∫ w(π ⊗ χ) (E_P^G ψ_{π ⊗ χ})(g) dρ(χ)`, an integral over `Im X(M_I)`.

## Proofs

Every result about `C^∞(O, P)` and `f_ψ` applies the corresponding `OrbitWavePacket` lemma, with
the same actual data as the definitions. The structural hypotheses of the bound are the same as
in Unit 19:

- `U_I(F)` is unimodular: `isUnimodularModulus_standardUnipotentPoints`;
- the Levi data: `rationalLeviData`;
- `δ₀ = 1` on `P₀(F) ∩ K`: `rationalMinimalModulus_eq_one`;
- `K` and `K ∩ M_I(F)` are compact: `compactSpace_subgroupOf_standardLevi`;
- `Ξ = xi hPK δ₀` holds by definition of `rationalXi`.

The Laurent property and the continuity of the coordinates are those proved here.

Technique, as in Unit 19:

- every Library lemma is instantiated with `(G := rationalPoints G)` and
  `(M := standardLeviPoints …)`;
- the definitions are unfolded (`unfold rationalInducedOrbitWavePacket`, and
  `unfold unitaryOrbitRepresentativeCoefficientMap` for the representative lemma);
- the final step is `with_reducible_and_instances exact`. The goal and the lemma then differ only
  by instance terms, and by the proof of `G(F) = P_I(F) K`, which is irrelevant.

## Scope and hypotheses

- Only standard parabolics `P_I ⊇ P₀` are covered; the semi-standard case is not formalized.
- The weight `w` replaces the Plancherel density `µ` of V.2. Neither `µ` nor its regularity is
  constructed here.
- The orbit data `C`, `mu` and `hsq` are general. The choice `C = A_{M_I}(F)` and the
  normalization of the measures (I.1, VI.3) are not fixed here. Finiteness of the stabilizer is
  an instance hypothesis.
- `K`, `hKc`, `hPK` and `hM` are data (ledger rows S3 and S5). `hcoeff` is a hypothesis: for `π`
  square integrable modulo the centre it is the conclusion of Corollary III.1.2, whose actual
  statement `RationalSquareIntegrableRapidDecayStatement` is not yet proved.
- Proposition VI.3.1 (`f_ψ ∈ C(G)`, and continuity of `ψ ↦ f_ψ`) is not proved here. The bound
  by `Ξ` above is the first step of its proof.
