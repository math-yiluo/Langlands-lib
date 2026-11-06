# The lattice map of Laurent torus coordinates

Lean module: `Langlands.HarmonicAnalysis.HarishChandraSchwartz.LaurentExponent`, namespace
`Langlands.HarishChandraSchwartz`. It imports:

- the published `Representation.Plancherel.UnitaryUnramifiedSmoothEvaluation` (Worker 200):
  `HasLaurentUnitaryCoordinates ν e`, the condition that for every `m : H` there is
  `n : J → ℤ` with `((e.symm z).val m : ℂ) = torusCharacter n z` for all `z : J → Circle`, and
  `rationalCanonicalUnitaryUnramifiedCharacterCoordinates_hasLaurent`; through its imports
  `commonNormKernel ν` with `mem_commonNormKernel`, `unitaryUnramifiedCharacters ν` and
  `rationalCanonicalUnitaryUnramifiedCharacterCoordinates`;
- `Langlands.HarmonicAnalysis.TorusFourierInversion`: `torusCharacter_zero`,
  `torusCharacter_add`, and through `TorusFourierDecay` the characters
  `torusCharacter n z = ∏ⱼ zⱼ^{nⱼ}`, `norm_torusCharacter`, `finiteTorusExp` and
  `torusCharacter_finiteTorusExp_single`;
- `Langlands.Topology.CompactNormCharacter`: `RankinSelberg.LastRowReduction.eq_one_of_isCompact`
  (a continuous homomorphism to `ℝ≥0ˣ` is trivial on a compact subgroup);
- `Langlands.HarmonicAnalysis.HarishChandraSchwartz.RationalValuationCoordinates`:
  `rationalValuationCoordinates G hG` and `rationalUnitaryUnramifiedCharacter_apply`.

## Provenance

J.-L. Waldspurger, *La formule de Plancherel pour les groupes p-adiques, d'après
Harish-Chandra*, J. Inst. Math. Jussieu 2 (2003), 235–333, DOI 10.1017/S1474748003000082
(literature id `waldspurger-2003-plancherel`).

- I.1, printed pp. 239–240 (PDF pp. 5–6): `G¹`, the unramified characters
  `X(G) = Hom(G/G¹, ℂ^×)` and the unitary subgroup `Im X(G)`.
- Proof of Proposition VII.1.3, printed p. 316 (PDF p. 82): the functions
  `χ ↦ C_{v⊗v̌, f}(χ)` on `Im X(G)` (quoted in `TwistedFourierFamily.md`).

Waldspurger has no coordinates on `Im X(G)`. All content of this module is derived. It supplies
the hypotheses on the lattice map `n` used by the Library's torus formulation of the proof of
Proposition VII.1.3: in `TwistedFourierFamily` and in the accepted candidate
`FourierOrbitSmoothness` (d6417274, not yet in the Library when this module was written), the
characters are `χ_z(m) = torusCharacter (n m) z` for a map `n` with
`hn : ∀ g h, n (g * h) = n g + n h`, `hK₀ : ∀ k ∈ K₀, n k = 0` for a compact open subgroup `K₀`,
`hnm : Measurable n` and the identification `hne` of `χ_z` with the coordinate character. This
module constructs such an `n` from `HasLaurentUnitaryCoordinates` and proves these properties.
It does not prove the growth bound `‖n(m)‖ ≤ C (1 + σ(m))` (`hnσ`), and it does not apply the
results to those modules.

## Scope and hypotheses

### Torus section

`J` is a finite type.

- `eq_zero_of_forall_torusCharacter_eq_one`: `k : J → ℤ` with
  `hk : ∀ z, torusCharacter k z = 1`.
- `torusCharacter_injective`: no further hypotheses.

### Laurent section

`H` is a group with a topology, `I` a type, `ν : I → (H →* ℝ≥0ˣ)`, `J` a finite type,
`e : unitaryUnramifiedCharacters ν ≃* (J → Circle)` a group isomorphism and
`he : HasLaurentUnitaryCoordinates ν e`. No continuity of `e` is assumed.

- `laurentExponent`, `torusCharacter_laurentExponent`, `laurentExponent_mul`: `ν`, `e`, `he`.
- `laurentExponent_eq_of_forall`: in addition `m : H`, `n : J → ℤ` and
  `hn : ∀ z, ((e.symm z).val m : ℂ) = torusCharacter n z`.
- `laurentExponent_eq_zero_of_mem`: `hm : m ∈ commonNormKernel ν`.
- `laurentExponent_eq_zero_of_isCompact`: `hν : ∀ i, Continuous (ν i)`, a subgroup `K₀` of `H`
  with `hK₀ : IsCompact (K₀ : Set H)`, and `hk : k ∈ K₀`.
- `laurentExponent_mul_of_mem`: `m : H` and `hk : k ∈ commonNormKernel ν`.
- `isLocallyConstant_laurentExponent`: `ContinuousMul H` and
  `hopen : IsOpen (commonNormKernel ν : Set H)`.
- `measurable_laurentExponent`: `ContinuousMul H`, a measurable space on `H` with
  `OpensMeasurableSpace H`, and `hopen`.

### Rational section

`F` is a nonarchimedean local field and `G` a group scheme over `F`;
`G(F) = GroupScheme.rationalPoints G` carries `rationalPointTopology F G.X`.

- `laurentExponent_rationalCanonical`: `hG : GroupScheme.IsConnectedReductive G` and
  `g : G(F)`. The affineness of `G.X.left` used by the topology is derived from `hG` inside the
  proof; it is not a hypothesis.

## Definitions

- `laurentExponent ν e he m : J → ℤ`, the exponent chosen (`Classical.choose`) from
  `he m`: a vector `n` with `χ_z(m) = ∏ⱼ zⱼ^{nⱼ}` for every `z`, where `χ_z = e.symm z`. By
  `laurentExponent_eq_of_forall` every such vector equals the chosen one.

## Results

- `eq_zero_of_forall_torusCharacter_eq_one`: if `∏ⱼ zⱼ^{kⱼ} = 1` for all `z`, then `k = 0`.
- `torusCharacter_injective`: `n ↦ torusCharacter n` is injective.
- `torusCharacter_laurentExponent`: `torusCharacter (laurentExponent ν e he m) z =
  ((e.symm z).val m : ℂ)`.
- `laurentExponent_eq_of_forall`: if `((e.symm z).val m : ℂ) = torusCharacter n z` for all `z`,
  then `laurentExponent ν e he m = n`.
- `laurentExponent_mul`: `laurentExponent ν e he (g * h) = laurentExponent ν e he g +
  laurentExponent ν e he h` (this is `hn`).
- `laurentExponent_eq_zero_of_mem`: `laurentExponent ν e he m = 0` for `m ∈ commonNormKernel ν`.
- `laurentExponent_eq_zero_of_isCompact`: `laurentExponent ν e he k = 0` for every element `k`
  of a compact subgroup, when every `ν i` is continuous (this gives `hK₀`).
- `laurentExponent_mul_of_mem`: `laurentExponent ν e he (m * k) = laurentExponent ν e he m` for
  `k ∈ commonNormKernel ν`.
- `isLocallyConstant_laurentExponent`: the map is locally constant when `commonNormKernel ν` is
  open.
- `measurable_laurentExponent`: the map is measurable when `commonNormKernel ν` is open (this
  gives `hnm`).
- `laurentExponent_rationalCanonical`: for the canonical rational coordinates
  `rationalCanonicalUnitaryUnramifiedCharacterCoordinates G hG` on `Im X(G)`, with norm
  characters `ψ ↦ (rationalNormCharacters G ψ).toMul` and Laurent condition
  `rationalCanonicalUnitaryUnramifiedCharacterCoordinates_hasLaurent G hG`,
  `laurentExponent … g = rationalValuationCoordinates G hG g`.

The identity `hne` holds for `n = laurentExponent ν e he` by `torusCharacter_laurentExponent`,
read with `unitaryTorusParameter ν e z` in place of `e.symm z`; that rewriting is not done in this
module.

## Proofs

- `eq_zero_of_forall_torusCharacter_eq_one`: if `kⱼ ≠ 0`, evaluate at
  `finiteTorusExp (Pi.single j (π / kⱼ))`; by `torusCharacter_finiteTorusExp_single` the value
  is `exp(kⱼ · (π / kⱼ) · i) = exp(π i) = -1 ≠ 1`.
- `torusCharacter_injective`: from `torusCharacter_add`, `torusCharacter (n - n') z ·
  torusCharacter n' z = torusCharacter n z = torusCharacter n' z`; the factor
  `torusCharacter n' z` has norm `1`, so it cancels and `n - n' = 0` by the previous lemma.
- `laurentExponent_mul`: by uniqueness, since `χ_z(g h) = χ_z(g) χ_z(h)` and
  `torusCharacter_add`.
- `laurentExponent_eq_zero_of_mem`: by uniqueness, since the characters in
  `unitaryUnramifiedCharacters ν` are trivial on `commonNormKernel ν` and
  `torusCharacter 0 = 1`. The compact case uses `eq_one_of_isCompact` for each `ν i`.
- `isLocallyConstant_laurentExponent`: the coset `m · commonNormKernel ν` is an open
  neighbourhood of `m` on which the map is constant (`laurentExponent_mul_of_mem`).
- `measurable_laurentExponent`: the fibres of a locally constant map are open, hence measurable,
  and `J → ℤ` is countable (`measurable_to_countable'`).
- `laurentExponent_rationalCanonical`: by uniqueness and
  `rationalUnitaryUnramifiedCharacter_apply`.
