# Lemma VI.2.2 on `C^∞(O, P)` and the wave packets `f_ψ` (Waldspurger, VI.2–VI.3)

Lean module: `Langlands.HarmonicAnalysis.HarishChandraSchwartz.OrbitWavePacket`, namespace
`Langlands.HarishChandraSchwartz`. It imports:

- `Langlands.HarmonicAnalysis.HarishChandraSchwartz.InducedCoefficientTwistXi` (Worker 249):
  `norm_family_coefficientMap_le_xi` (the uniform `Ξ`-bound for smooth families in the compact
  picture), `twistedSection` and `factorization_subtype`; through its imports `xi`, `LeviData`,
  `IsIwasawaPair`, `iwasawaWeight_nonneg`, Worker 200's `CompactInduction.coefficientMap`,
  `ProductInducedCompactPicture`, `productInducedCompactEquiv` and `finiteSmoothFamilies`;
- `Langlands.Representation.Plancherel.ProductInducedOrbitCoefficientSmoothness` (Worker 200):
  `continuous_unitaryOrbitCoefficient` (continuity in `ω` of the coefficient, from Lemma
  VI.2.1 (i)); through its imports `HasLaurentUnitaryCoordinates`,
  `ProductInducedOrbitCoefficients` (`unitaryOrbitCoefficientMap`,
  `unitaryOrbitRepresentativeCoefficientMap`, `unitaryOrbitRepresentativeCoefficientMap_transport`,
  `unitaryOrbitCoefficientMap_representative`, `unitaryOrbitCoefficientMap_biInvariant`),
  `ProductInducedOrbitSections` (`productInducedSmoothOrbitSections`,
  `UnitaryOrbitRepresentative`, `unitaryOrbitParameterRepresentative`,
  `unitaryOrbitRepresentativeParameter`, `unitaryOrbitRepresentativeEquiv`,
  `productInducedOrbitPullback`), `ProductInducedSmoothFamilies` (`unitaryTorusParameter`,
  `productInducedFamilyRestriction`) and `ProductInducedDiscreteSeriesOrbit`
  (`unitaryOrbitRepresentativeDiscreteSeriesOrbit_surjective`);
- `Langlands.Representation.Plancherel.DiscreteSeriesOrbitMeasure`: the orbit measure
  `discreteSeriesOrbitMeasure` with `discreteSeriesOrbitMeasure_univ`, the Borel structures on
  the orbit and on the unitary unramified characters; through its imports the orbit
  `discreteSeriesOrbit`, the orbit map `discreteSeriesOrbitMap` with
  `continuous_discreteSeriesOrbitMap`, the stabilizer `discreteSeriesStabilizer` and
  `discreteSeriesClass`.

## Provenance

J.-L. Waldspurger, *La formule de Plancherel pour les groupes p-adiques, d'après
Harish-Chandra*, J. Inst. Math. Jussieu 2 (2003), 235–333, DOI 10.1017/S1474748003000082
(literature id `waldspurger-2003-plancherel`). Printed page numbers; the PDF page is the printed
page minus 234.

- Lemma VI.2.2, printed p. 298 (PDF p. 64): "Soit `ψ ∈ C^∞(O, P)`. Il existe `C > 0` tel que
  pour tout `ω ∈ O` et tout `g ∈ G`, on ait l'inégalité `|(E_P^G ψ_ω)(g)| ≤ C Ξ(g)`." The proof
  begins: "On se ramène facilement à prouver l'assertion suivante: soient `(ω, E) ∈ O`,
  `v ∈ I_{K∩P}^K E`, `v̌ ∈ I_{K∩P}^K Ě`; alors il existe `C > 0` tel que pour tous
  `χ ∈ Im X(M)` et tout `g ∈ G`, on ait `|⟨I_P^G(ω ⊗ χ)(g) v, v̌⟩| ≤ C Ξ(g)`." The reduced
  assertion is `norm_family_coefficientMap_le_xi` (`InducedCoefficientTwistXi`). This module
  carries out the reduction "on se ramène facilement" for Worker 200's `C^∞(O, P)`.
- VI.3, printed p. 302 (PDF p. 68): "On a muni `Im X(M)` d'une mesure. On munit `O` d'une mesure
  telle que l'application `Im X(M) → O`, `χ ↦ ω ⊗ χ` préserve localement les mesures. Pour
  `ψ ∈ C^∞(O, P)` définissons une fonction `f_ψ` sur `G` par
  `f_ψ(g) = ∫_O µ(ω) (E_P^G ψ_ω)(g) dω`."

`exists_norm_unitaryOrbitCoefficientMap_le_xi` is Lemma VI.2.2 (source content) in the
Library's formulation, and `exists_norm_unitaryOrbitRepresentativeCoefficientMap_le_xi` is the
same bound at every representative instead of every class. `inducedOrbitWavePacket` is the
function `f_ψ` of VI.3 with two generalizations:

- the Plancherel density `µ` of V.2 (printed p. 292, `µ(ω) = j(ω)^{-1} ∏ γ(M_α|M)^2`) is not in
  the Library; the definition takes an arbitrary weight `w : O → ℂ` in its place;
- the orbit measure is `discreteSeriesOrbitMeasure` for an arbitrary measure `ρ` on the unitary
  unramified characters. It is `|S|⁻¹` times the push-forward of `ρ` along `χ ↦ ω ⊗ χ`, where
  `S` is the finite stabilizer of `ω`. For left-invariant `ρ` the Library's
  `isLocallyMeasurePreserving_discreteSeriesOrbitMap` is Waldspurger's condition that the orbit
  map preserves measures locally; Waldspurger's choice is a Haar measure `ρ`.

The other results (finiteness of the orbit measure, the bound `|f_ψ| ≤ c Ξ`, bi-invariance,
integrability, linearity and the formula as an integral over the characters) are derived: they
are the first properties of `f_ψ` used in the proof of Proposition VI.3.1 (printed p. 302), not
statements of the paper. `unitaryTorusParameter_injective` and
`norm_unitaryTorusParameter_apply` are derived facts about the Library's torus coordinates.

## Scope and hypotheses

Section variables (those of `ProductInducedOrbitCoefficients`): a group `G` with a topology,
`[LocallyCompactSpace G]`, `[NonarchimedeanGroup G]`, `[SecondCountableTopology G]`,
`[T2Space G]`, `[MeasurableSpace G]`, `[BorelSpace G]`; subgroups `P`, `M`, `U` of `G` with
`[LocallyCompactSpace P]`; `h : IsSemidirectDecomposition P M U`, `hU : IsClosed U`,
`hP : IsClosed P`; an open subgroup `K` with `hK : IsCompact K` and
`hPK : ∀ g, ∃ p : P, ∃ k : K, g = p k`; `hG : ∀ g, modularCharacter g = 1`;
`hδ : ∀ p : P, modularCharacter p = closedRestrictCharacter U hU P … p`; a type `I`,
`ν : I → (M →* ℝ≥0ˣ)` with `hν : ∀ i, Continuous (ν i)`; `π : IrreducibleAdmissibleRep ℂ M`;
`hr : Continuous h.projection`; a finite type `J` and torus coordinates
`e : unitaryUnramifiedCharacters ν ≃* (J → Circle)`; a subgroup `P₀` of `G` with
`δ₀ : P₀ →* ℝ≥0ˣ` and `δ₀M : P₀ ∩ M →* ℝ≥0ˣ`; `[CompactSpace K]` and `[CompactSpace (K ∩ M)]`.
The linter `omit`s the unused ones from each statement.

The orbit data (sections `Bound`, after the first theorem, and `WavePacket`): a normal subgroup
`C` of `M` with `hC : C ≤ center M`, a measurable structure on `M/C` with a Haar measure `μ`,
and `hsq : IsSquareIntegrableModCentralSubgroup C hC π μ`, so that `O` is
`discreteSeriesOrbit C hC μ ν (discreteSeriesClass C hC μ π hsq)`. In section `WavePacket`
also `[Finite (discreteSeriesStabilizer … )]` (the stabilizer `S` of the class of `π`), a
measure `ρ` on `unitaryUnramifiedCharacters ν` and a weight `w : O → ℂ`.

The hypotheses of the bound (those of `norm_family_coefficientMap_le_xi`):
`hδU : IsUnimodularModulus U hU`; `hL : LeviData K P₀ P M δ₀ (closedRestrictCharacter U hU M …)
δ₀M h.projection`; the Iwasawa pairs `hP₀K : IsIwasawaPair P₀ K` and
`hMK : IsIwasawaPair (P₀ ∩ M) (K ∩ M)`; `hδ₀ : ∀ p : P₀, p ∈ K → δ₀ p = 1`; and
`hcoeff : ∀ v ℓ, ∃ c > 0, ∀ m, ‖ℓ(π(m) v)‖ ≤ c Ξ^M(m)` with `Ξ^M = xi hMK δ₀M` (the conclusion of
Corollary III.1.2 for `π`, used in the proof of Lemma VI.2.2). `Ξ` is `xi hP₀K δ₀`.

- `unitaryTorusParameter_injective`, `norm_unitaryTorusParameter_apply`: no hypotheses beyond the
  types.
- `exists_norm_unitaryOrbitRepresentativeCoefficientMap_le_xi`: `hδU`, `hL`, `hP₀K`, `hMK`,
  `hδ₀`, `hcoeff` and `q : productInducedSmoothOrbitSections ν π e h hU K hP hK hν hr hPK`.
- `exists_norm_unitaryOrbitCoefficientMap_le_xi`: the same and the orbit data `C`, `hC`, `μ`,
  `hsq`.
- `inducedOrbitWavePacket` (definition): the orbit data, `[Finite S]`, `ρ`, `w`, `q` and `g`.
- `isFiniteMeasure_discreteSeriesOrbitMeasure`: `[IsFiniteMeasure ρ]`.
- `exists_norm_inducedOrbitWavePacket_le_xi`: `[IsFiniteMeasure ρ]`, a real `b` with
  `hw : ∀ ω, ‖w ω‖ ≤ b`, `hδU`, `hL`, `hP₀K`, `hMK`, `hδ₀`, `hcoeff` and `q`.
- `exists_inducedOrbitWavePacket_biInvariant`: only `q`.
- `integrable_inducedOrbitWavePacket_integrand`: `[IsFiniteMeasure ρ]`,
  `hLaurent : HasLaurentUnitaryCoordinates ν e`, `he : Continuous e`,
  `hwm : AEStronglyMeasurable w (discreteSeriesOrbitMeasure … ρ)`, `hw`, `hδU`, `hL`, `hP₀K`,
  `hMK`, `hδ₀`, `hcoeff`, `q` and `g`.
- `inducedOrbitWavePacket_smul`: `c : ℂ`, `q`, `g`.
- `inducedOrbitWavePacket_add`: the hypotheses of `integrable_inducedOrbitWavePacket_integrand`,
  with two sections `q r`.
- `inducedOrbitWavePacketLinear` (definition): the hypotheses of
  `integrable_inducedOrbitWavePacket_integrand` without `q` and `g`.
- `inducedOrbitWavePacket_eq_parameterIntegral`: `hLaurent`, `he`, `hwm`, `q`, `g` (no
  finiteness of `ρ`).

## Definitions

- `inducedOrbitWavePacket … ρ w q : G → ℂ`, `g ↦ ∫_O w(ω) (E_P^G q_ω)(g) dω` for the measure
  `discreteSeriesOrbitMeasure ν C hC μ (discreteSeriesClass C hC μ π hsq) ρ`, where
  `(E_P^G q_ω)(g)` is `unitaryOrbitCoefficientMap … q ω g`.
- `inducedOrbitWavePacketLinear … : productInducedSmoothOrbitSections … →ₗ[ℂ] (G → ℂ)`,
  `q ↦ inducedOrbitWavePacket … q`.

## Results

- `unitaryTorusParameter_injective`: `z ↦ unitaryTorusParameter ν e z` is injective.
- `norm_unitaryTorusParameter_apply`: `‖(unitaryTorusParameter ν e z) m‖ = 1`.
- `exists_norm_unitaryOrbitRepresentativeCoefficientMap_le_xi`: there is `c > 0` such that for
  every representative `A : UnitaryOrbitRepresentative ν π` and every `g`,
  `‖unitaryOrbitRepresentativeCoefficientMap … A (q A) g‖ ≤ c Ξ(g)`.
- `exists_norm_unitaryOrbitCoefficientMap_le_xi` (**Lemma VI.2.2**): there is `c > 0` such that
  `‖(E_P^G q_ω)(g)‖ ≤ c Ξ(g)` for all `ω ∈ O` and `g ∈ G`.
- `isFiniteMeasure_discreteSeriesOrbitMeasure`: the orbit measure of a finite `ρ` is finite.
- `exists_norm_inducedOrbitWavePacket_le_xi`: there is `c > 0` with `‖f_ψ(g)‖ ≤ c Ξ(g)` for all
  `g`.
- `exists_inducedOrbitWavePacket_biInvariant`: there is a compact open subgroup `H ≤ K` with
  `f_ψ(k g l) = f_ψ(g)` for all `k, l ∈ H` and `g ∈ G`.
- `integrable_inducedOrbitWavePacket_integrand`: `ω ↦ w(ω) (E_P^G q_ω)(g)` is integrable for the
  orbit measure.
- `inducedOrbitWavePacket_smul`: `f_{c q}(g) = c f_q(g)`.
- `inducedOrbitWavePacket_add`: `f_{q + r}(g) = f_q(g) + f_r(g)`.
- `inducedOrbitWavePacket_eq_parameterIntegral`:
  `f_ψ(g) = |S|⁻¹ ∫ w(ω ⊗ χ) (E_P^G q_{ω ⊗ χ})(g) dρ(χ)`, with `ω ⊗ χ` written
  `discreteSeriesOrbitMap … χ` and `|S|` the cardinality `Nat.card` of the stabilizer.

## Proof notes

1. `unitaryTorusParameter ν e` is `unitaryUnramifiedInclusion ν ∘ e.symm`, a composition of
   injective maps; its values are unitary by the membership proof of `e.symm z`.
2. Representative bound. For a section `q`, the restricted family
   `R = productInducedFamilyRestriction (productInducedOrbitPullback q)` lies in
   `finiteSmoothFamilies` by the definition of `productInducedSmoothOrbitSections`, so
   `norm_family_coefficientMap_le_xi` with `Ψ := R` and the left inverse
   `Function.invFun (unitaryTorusParameter ν e)` gives one constant `c` for all twists of `π` by
   unitary torus parameters. For a representative `A`, with `z` its chosen parameter and `B` the
   parameter representative at `z`, coherence gives `q A = transport (q B)`, and
   `unitaryOrbitRepresentativeCoefficientMap_transport` reduces to `B`. At `B`, `twistedSection`
   of `R z` is `q B` (`productInducedCompactEquiv … |>.symm_apply_apply`). The final `exact`
   needs `set_option maxRecDepth 10000` and `set_option maxHeartbeats 1000000` (the twisted
   representation `π.obj.twist …` is matched against the object of the parameter representative
   `B`).
3. Orbit bound: every `ω ∈ O` is the class of a representative
   (`unitaryOrbitRepresentativeDiscreteSeriesOrbit_surjective`), and
   `unitaryOrbitCoefficientMap_representative` identifies the coefficients.
4. Finiteness: `discreteSeriesOrbitMeasure_univ` and `Nat.card_pos`.
5. Wave packet bound: `norm_integral_le_of_norm_le_const` with the pointwise bound
   `|b| c Ξ(g)` and the total mass `r` of the orbit measure; the constant is `1 + |b| c r`.
6. Bi-invariance: the subgroup of `unitaryOrbitCoefficientMap_biInvariant` fixes every integrand.
7. Integrability: `Integrable.of_bound` with `hwm` times the continuity of
   `continuous_unitaryOrbitCoefficient` (which needs `hLaurent` and `he`).
8. Linearity: `unitaryOrbitCoefficientMap` is linear in `q`; homogeneity is
   `integral_const_mul`, additivity is `integral_add` with step 7.
9. Parameter integral: the orbit measure is `|S|⁻¹ • map (discreteSeriesOrbitMap …) ρ`;
   `integral_smul_measure` and `integral_map`. The strong measurability of the integrand for the
   push-forward follows from `hwm` because `|S|⁻¹ ≠ 0` (`Measure.ae_ennreal_smul_measure_iff`).

## Relation to the Library

- `rationalOrbitWavePacket` (`RationalOrbitWavePacketPairing`, Worker 249) is the wave packet for
  `M = G` with the I.1 orbit measure, on sections given by coefficient tensors of chosen
  representatives; there `µ = 1`. This module treats a general `P = M U` with Worker 200's
  section space `C^∞(O, P)`.
- `InducedCoefficientTwistXi` proves the bound for smooth families in the compact picture and
  states that the passage to `C^∞(O, P)` is not done there; this module does it.
- Lemma VI.2.1 (i) (smoothness and continuity of `ω ↦ (E_P^G ψ_ω)(g)`) is Worker 200's
  `ProductInducedOrbitCoefficientSmoothness`; it is used, not reproved.

## Open obligations

- The Plancherel density `µ` (V.2) is not in the Library; `w` stands in for it. With
  `w = µ` one needs `µ` bounded and measurable on `O` (Waldspurger: `µ` is regular, so continuous,
  on the compact orbit).
- Proposition VI.3.1 (`f_ψ ∈ C(G)` and continuity of `ψ ↦ f_ψ`) is not addressed; the bound
  `|f_ψ| ≤ c Ξ` is the first step, without the factor `(1 + σ)^{-r}`.
- `hcoeff` (Corollary III.1.2 for `π`) and the Iwasawa and Levi data `hL`, `hP₀K`, `hMK`, `hδ₀`
  are hypotheses.
