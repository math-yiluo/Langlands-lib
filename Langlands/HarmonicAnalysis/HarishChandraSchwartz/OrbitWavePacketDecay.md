# The first bound in the proof of Prop. VI.3.1 for the wave packets `f_ψ` (Waldspurger, VI.3)

Lean module: `Langlands.HarmonicAnalysis.HarishChandraSchwartz.OrbitWavePacketDecay`, namespace
`Langlands.HarishChandraSchwartz`. It imports:

- `Langlands.HarmonicAnalysis.HarishChandraSchwartz.OrbitWavePacket` (Worker 249): the wave
  packet `inducedOrbitWavePacket` (`f_ψ`), `inducedOrbitWavePacket_eq_parameterIntegral`,
  `norm_unitaryTorusParameter_apply`; through its imports `xi`, `LeviData`, `IsIwasawaPair`,
  `iwasawaWeight_nonneg`, `norm_twist_coefficientMap_le_xi`, `twistedSection`,
  `compactValue_twistedSection`, `coefficientTensorMap_twist`, `factorization_subtype`
  (`InducedCoefficientTwistXi`), Worker 200's `CompactInduction.coefficientMap`,
  `CompactInduction.coefficientMap_integral`, `CompactInduction.integrand`,
  `CompactInduction.integrand_factorization`, `CompactInduction.integrand_isLocallyConstant`,
  `CompactInduction.integrand_integrable`, `CompactInduction.measure`,
  `ProductInducedCompactPicture`, `productInducedCompactEquiv`, `finiteSmoothFamilies` with
  `mem_finiteSmoothFamilies_iff`, `productInducedSmoothOrbitSections`,
  `productInducedFamilyRestriction`, `productInducedOrbitPullback`, `unitaryTorusParameter`,
  `unitaryOrbitParameterRepresentative`, `unitaryOrbitCoefficientMap` with
  `unitaryOrbitCoefficientMap_parameter`, `unitaryOrbitRepresentativeCoefficientMap`,
  `HasLaurentUnitaryCoordinates`, and the orbit data `discreteSeriesOrbit`,
  `discreteSeriesOrbitMap`, `isOpenQuotientMap_discreteSeriesOrbitMap`,
  `discreteSeriesOrbitMeasure`, `discreteSeriesStabilizer`, `discreteSeriesClass`;
- `Langlands.Representation.Plancherel.ProductInducedOrbitBaseChange` (Worker 200):
  `unitaryTorusParameter_mul`;
- `Langlands.HarmonicAnalysis.TorusFourierAveraging` (Worker 249): `norm_integral_mul_le_rpow`
  (the averaging estimate over a torus of twists); through its imports `torusCharacter` and
  `continuous_torusCharacter`;
- `Langlands.HarmonicAnalysis.TorusFourierInversion` (Worker 249): `torusCharacter_zero`,
  `torusCharacter_add`;
- `Langlands.HarmonicAnalysis.TorusMonomialDerivative` (Worker 249, this submission):
  `continuous_finiteTorusMonomial`, `isSmoothFiniteTorusFunction_comp_monomial_mul`,
  `exists_bound_comp_monomial_mul`.

## Provenance

J.-L. Waldspurger, *La formule de Plancherel pour les groupes p-adiques, d'après
Harish-Chandra*, J. Inst. Math. Jussieu 2 (2003), 235–333, DOI 10.1017/S1474748003000082
(literature id `waldspurger-2003-plancherel`). Printed page numbers; the PDF page is the printed
page minus 234.

Proof of Proposition VI.3.1, printed p. 303 (PDF p. 69): "Pour `χ ∈ Im X(M)`, `λ ∈ Im X(G)` et
`g ∈ G`, on a `(E^G_P sp_{λχ} ψ)(g) = λ(g)(E^G_P sp_χ ψ)(g)`. Pour `g ∈ G` et
`ϕ ∈ C^∞(Im X(M))`, définissons une fonction `ϕ_g` sur `Im X(M)` par
`ϕ_g(χ) = ∫_{Im X(G)} ϕ(λχ) λ(g) dλ`. (3) Alors
`f_{ϕ,ψ}(g) = ∫_{Im X(G)\Im X(M)} µ(ω ⊗ χ) ϕ_g(χ) (E^G_P sp_χ ψ)(g) dχ`. La théorie usuelle de
la transformation de Fourier sur le groupe abélien compact `Im X(G)` nous dit qu'il existe
`D ∈ D_G` tel que pour tout `ϕ' ∈ C^∞(Im X(G))` et tout `g ∈ G`, on ait
`|∫_{Im X(G)} ϕ'(λ) λ(g) dλ| ≤ (1 + (H_G(g)))^{-r} ν_G(D, ϕ')`. (4) En utilisant le Lemme
VI.2.2, on en déduit qu'il existe `D ∈ D_M` tel que pour tout `ϕ ∈ C^∞(Im X(M))` et tout
`g ∈ G`, on ait l'inégalité `|f_{ϕ,ψ}(g)| ≤ (1 + |H_G(g)|)^{-r} Ξ(g) ν_M(D, ϕ)`."

- `twistedSectionCoefficient_mul` is the displayed identity
  `(E^G_P sp_{λχ} ψ)(g) = λ(g)(E^G_P sp_χ ψ)(g)` (source content), stated for the coefficient
  of the transports `twistedSection χ F₀` of one fixed section `F₀` of the compact picture
  (Waldspurger's `v_χ` in the proof of Lemma VI.2.2, printed p. 298), and for any character `Λ`
  of `G` trivial on `K` and `U` whose restriction to `M` is `θ` (in place of `λ ∈ Im X(G)`).
- `exists_norm_inducedOrbitWavePacket_le_xi_rpow` is the final inequality of the quotation for
  the wave packet `f_ψ = inducedOrbitWavePacket` of `OrbitWavePacket`, with these differences:
  - The weight. Waldspurger's integrand over `Im X(M)` is `µ(ω ⊗ χ) ϕ(χ)`; the Plancherel
    density `µ` of V.2 is not in the Library. As in `OrbitWavePacket`, an arbitrary weight
    `w : O → ℂ` on the orbit stands in for `µ ϕ`, and the theorem assumes `w` smooth in the
    torus coordinates (`hws`). Waldspurger's `f_ψ` of VI.3 is the case `w = µ`.
  - The constant. Waldspurger bounds `|f_{ϕ,ψ}(g)|` by a continuous seminorm `ν_M(D, ϕ)` of
    `ϕ`; the theorem gives a constant `c` depending on all the data (`w`, `q`, `r`, …), for
    one fixed `w`. Continuity in `ϕ` is not stated.
  - `H_G`. Waldspurger's `|H_G(g)|` is a norm of `H_G(g) ∈ 𝔞_G`. The theorem uses a homomorphism
    `n_G : G → ℤ^L` (written `nG : G →* Multiplicative (L → ℤ)`) together with the sup norm
    `‖n_G(g)‖` on `L → ℤ`; `n_G` stands for `H_G` in lattice coordinates and is not
    constructed. The characters of `Im X(G)` are written `g ↦ z^{n_G(g)}` (`latticeTorusCharacter`)
    for `z : L → Circle`, the torus `Im X(G)` in coordinates. The comparison between `‖n_G(g)‖`
    and `|H_G(g)|` for the actual `H_G` is not formalized.
  - The restriction `Im X(G) → Im X(M)` is an integer monomial map `finiteTorusMonomial a` in
    the torus coordinates `e` of `Im X(M)`, stated as hypothesis `hnM`.
  - The measure `ρ` on `Im X(M)` is any finite left invariant measure (Waldspurger: a Haar
    measure). The averaging over `Im X(G)` uses an auxiliary Haar probability measure on
    `L → Circle` that does not appear in the statement; Waldspurger's `dλ` in (3)–(4) has
    total mass `d_G` (I.1), which only changes the constant.

`latticeTorusCharacter`, `twistedSectionCoefficient`, `integrand_twistedSection_mul`,
`twistedSectionCoefficient_eq_integral` and `continuous_twistedSectionCoefficient` are derived
definitions and facts used in the proof (the coefficient of `v_χ` as a function of `χ`, its
integral formula and its continuity in `χ`); they are not statements of the paper.

## Scope and hypotheses

Section `Lattice`: a group `G`, a finite type `L`, `n : G →* Multiplicative (L → ℤ)`.

Section `Twist` (variables of `norm_twist_coefficientMap_le_xi`): a group `G` with a topology,
`[LocallyCompactSpace G]`, `[NonarchimedeanGroup G]`, `[SecondCountableTopology G]`,
`[T2Space G]`, `[MeasurableSpace G]`, `[BorelSpace G]`; subgroups `P`, `M`, `U` with
`[LocallyCompactSpace P]`, `h : IsSemidirectDecomposition P M U`, `hU : IsClosed U`,
`hP : IsClosed P`, `hm : Continuous h.projection`; `A : SmoothRep ℂ M` with
`hA : A.IsAdmissible`; an open subgroup `K` with `hK : IsCompact K` and
`hPK : ∀ g, ∃ q ∈ P, ∃ k ∈ K, g = q k`; `hG : ∀ g, modularCharacter g = 1`;
`hδP : ∀ q : P, modularCharacter q = closedRestrictCharacter U hU P … q`; a type `I`,
`ν : I → (M →* ℝ≥0ˣ)` with `hν : ∀ i, Continuous (ν i)`.

- `twistedSectionCoefficient` (definition), `twistedSectionCoefficient_apply`,
  `twistedSectionCoefficient_eq_integral`: all of these, a character
  `χ : unramifiedCharacters ν` (and `F₀`, `g`).
- `integrand_twistedSection_mul`: `h`, `hU`, `A`, `K`, `hK`, `ν`, `hν`, `hP`, `hm`, `hPK` and
  `[SecondCountableTopology G]` (the statement omits `[T2Space G]`, `[MeasurableSpace G]`,
  `[BorelSpace G]`, `[LocallyCompactSpace P]`); characters `θ χ`, `F₀`, `g`, `k k₁ : K`,
  `q : P` and `he : k g = q k₁`.
- `twistedSectionCoefficient_mul`: the section variables, `θ χ : unramifiedCharacters ν`,
  `Λ : G →* ℂ` with `hΛK : ∀ k ∈ K, Λ k = 1`, `hΛU : ∀ u ∈ U, Λ u = 1` and
  `hΛM : ∀ m : M, θ(m) = Λ(m)`; `F₀`, `g`.
- `continuous_twistedSectionCoefficient`: the section variables, a topological space `Y` with
  `[FirstCountableTopology Y]`, `χ : Y → unramifiedCharacters ν` with
  `hχ : ∀ m, Continuous (y ↦ χ_y(m))` and `hχu : ∀ y m, ‖χ_y(m)‖ = 1`; `F₀`, `g`.

Section `Orbit` (variables of `OrbitWavePacket`): the variables of section `Twist` with
`hPK : ∀ g, ∃ p : P, ∃ k : K, g = p k`, `hδ` in place of `hδP` and `hr` in place of `hm`, an
irreducible admissible `π : IrreducibleAdmissibleRep ℂ M` in place of `A`, a finite type `J`
with torus coordinates `e : unitaryUnramifiedCharacters ν ≃* (J → Circle)`, a subgroup `P₀`
with `δ₀ : P₀ →* ℝ≥0ˣ` and `δ₀M : P₀ ∩ M →* ℝ≥0ˣ`, `[CompactSpace K]`,
`[CompactSpace (K ∩ M)]`; the orbit data `C`, `[C.Normal]`, `hC : C ≤ center M`, a measurable
structure on `M/C` with a Haar measure `μ`, `hsq : IsSquareIntegrableModCentralSubgroup C hC π μ`,
`[Finite S]` for the stabilizer `S = discreteSeriesStabilizer … (discreteSeriesClass … π hsq)`;
a measure `ρ` on `unitaryUnramifiedCharacters ν` and a weight `w : O → ℂ` on the orbit
`O = discreteSeriesOrbit … (discreteSeriesClass … π hsq)`.

`exists_norm_inducedOrbitWavePacket_le_xi_rpow` assumes, besides these:

- `[IsFiniteMeasure ρ]`, `[ρ.IsMulLeftInvariant]`;
- `hLaurent : HasLaurentUnitaryCoordinates ν e` and `he : Continuous e`;
- `hws : IsSmoothFiniteTorusFunction (y ↦ w(discreteSeriesOrbitMap … (e.symm y)))`;
- a finite type `L`, `nG : G →* Multiplicative (L → ℤ)` and an integer matrix `a : J → L → ℤ`
  with `hnK : ∀ k ∈ K, nG k = 1`, `hnU : ∀ u ∈ U, nG u = 1` and
  `hnM : ∀ (m : M) (z : L → Circle), (e.symm (finiteTorusMonomial a z))(m) =
  torusCharacter (nG m) z`;
- the hypotheses of Lemma VI.2.2 in `OrbitWavePacket`: `hδU : IsUnimodularModulus U hU`,
  `hL : LeviData K P₀ P M δ₀ (closedRestrictCharacter U hU M …) δ₀M h.projection`,
  `hP₀K : IsIwasawaPair P₀ K`, `hMK : IsIwasawaPair (P₀ ∩ M) (K ∩ M)`,
  `hδ₀ : ∀ p : P₀, p ∈ K → δ₀ p = 1`, and
  `hcoeff : ∀ v ℓ, ∃ c > 0, ∀ m, ‖ℓ(π(m) v)‖ ≤ c Ξ^M(m)` with `Ξ^M = xi hMK δ₀M`;
- a section `q : productInducedSmoothOrbitSections ν π e h hU K hP hK hν hr hPK` and `r : ℝ`.

`Ξ` is `xi hP₀K δ₀`.

## Definitions

- `latticeTorusCharacter n z : G →* ℂ`, `g ↦ torusCharacter (n g) z = ∏ₗ z_l^{n(g)_l}`.
- `twistedSectionCoefficient … χ : ProductInducedCompactPicture h K A →ₗ[ℂ] LocallyConstant G ℂ`,
  `F₀ ↦ CompactInduction.coefficientMap … (A ⊗ χ) (twistedSection … χ F₀)`: the coefficient
  `g ↦ ⟨I_P^G(A ⊗ χ)(g) v_χ, v̌_χ⟩` of the transport of `F₀` to the twist `A ⊗ χ`.

## Results

- `latticeTorusCharacter_apply`: the defining formula.
- `twistedSectionCoefficient_apply`: the defining formula.
- `integrand_twistedSection_mul`: for a factorization `k g = q k₁` (`q ∈ P`, `k₁ ∈ K`), the
  diagonal integrand `CompactInduction.integrand` at `k` of the transport of `F₀` to `A ⊗ θχ`
  is `θ(m(q))` times the one for `A ⊗ χ`, where `m(q) = h.projection q`.
- `twistedSectionCoefficient_eq_integral`: the coefficient at `g` is
  `∫_K integrand(k) d(CompactInduction.measure K hK)`.
- `twistedSectionCoefficient_mul`: `coeff_{θχ}(F₀)(g) = Λ(g) coeff_χ(F₀)(g)`.
- `continuous_twistedSectionCoefficient`: `y ↦ coeff_{χ_y}(F₀)(g)` is continuous.
- `exists_norm_inducedOrbitWavePacket_le_xi_rpow`: there is `c > 0` with
  `‖f_ψ(g)‖ ≤ c Ξ(g) (1 + ‖n_G(g)‖)^{-r}` for all `g ∈ G`, where
  `f_ψ = inducedOrbitWavePacket … ρ w q`.

## Proof notes

1. `latticeTorusCharacter` is a monoid hom by `torusCharacter_zero` and `torusCharacter_add`.
2. `integrand_twistedSection_mul`: for each character `χ'`, `integrand_factorization`,
   `compactValue_twistedSection`, `coefficientTensorMap_twist` and `apply_symm_apply` write the
   integrand as `δ_P^{1/2}(q) χ'(m(q)) ⟨F₀(k₁, k)⟩(m(q))`, the last factor independent of `χ'`.
   The two instances `χ' = θχ` and `χ' = χ` are rewritten separately, and
   `(θχ)(m) = θ(m) χ(m)` (`Subgroup.coe_mul`, `ContinuousMonoidHom.mul_apply`,
   `Units.val_mul`).
3. `twistedSectionCoefficient_mul`: by step 2 under the integral (`integral_const_mul`); for
   `k g = q k₁`, `Λ(g) = Λ(q)` because `Λ` is trivial on `K`, and `Λ(q) = Λ(m(q)) = θ(m(q))`
   because `m(q)⁻¹ q ∈ U` (`projection_inv_mul_mem`) and `Λ` is trivial on `U`.
4. `continuous_twistedSectionCoefficient`: by step 2 with `θ = χ_y` and the trivial character,
   the integrand is `χ_y(m(q_k))` times an integrand independent of `y`, for a chosen
   factorization `k g = q_k k₁`; `continuous_of_dominated` with the bound given by the norm of
   that integrand (integrable on `K`, `CompactInduction.integrand_integrable`) and `‖χ_y‖ = 1`.
5. Main theorem.
   - `W(y) = w(ω ⊗ e⁻¹(y))` is smooth, hence continuous; `w` is continuous because the orbit
     map is an open quotient map (`isOpenQuotientMap_discreteSeriesOrbitMap`), hence
     a.e. strongly measurable for the orbit measure.
   - The restricted family `R` of `q` lies in `finiteSmoothFamilies`; write
     `R(y) = ∑ᵢ fᵢ(y) vᵢ` with smooth `fᵢ` (`mem_finiteSmoothFamilies_iff`). By
     `unitaryOrbitCoefficientMap_parameter`, the inverse of `productInducedCompactEquiv`, and
     linearity of `twistedSectionCoefficient`,
     `(E^G_P q_{ω ⊗ χ_y})(g) = ∑ᵢ fᵢ(y) coeff_{χ_y}(vᵢ)(g)` with `χ_y = unitaryTorusParameter ν e y`.
   - `inducedOrbitWavePacket_eq_parameterIntegral` and `integral_map` along `e` give
     `f_ψ(g) = |S|⁻¹ ∑ᵢ ∫ W(y) fᵢ(y) coeff_{χ_y}(vᵢ)(g) dμ_T(y)` with `μ_T = e_* ρ`, finite
     and left invariant (`Measure.isFiniteMeasure_map`, `isMulLeftInvariant_map`).
   - Each integral is bounded by `norm_integral_mul_le_rpow` on `T = J → Circle` with
     `ι = finiteTorusMonomial a`, `φ = W fᵢ`, `F(y) = coeff_{χ_y}(vᵢ)(g)`, `n = n_G(g)`, an
     auxiliary Haar probability measure on `L → Circle`, `k = ⌈r⌉₊`:
     `F(ι(z) y) = z^{n_G(g)} F(y)` is step 3 with `Λ = latticeTorusCharacter nG z` (trivial on
     `K`, `U` by `hnK`, `hnU`; equal on `M` to the character with coordinates `ι(z)` by `hnM`)
     and `unitaryTorusParameter_mul`; continuity of `F` is step 4 (with `hLaurent` for the
     continuity of `y ↦ χ_y(m)` and `norm_unitaryTorusParameter_apply`); the derivative bounds
     are `exists_bound_comp_monomial_mul` and `isSmoothFiniteTorusFunction_comp_monomial_mul`;
     the bound `|F| ≤ Bᵢ Ξ(g)` is `norm_twist_coefficientMap_le_xi` for `vᵢ`.
   - Summing, `c = 1 + |S|⁻¹ ∑ᵢ 2^k (1 + |L|) Mᵢ μ_T(T) Bᵢ`. The proof needs
     `set_option maxRecDepth 10000` and `set_option maxHeartbeats 2000000`; the definition
     `twistedSectionCoefficient` and `twistedSectionCoefficient_apply` need
     `set_option maxHeartbeats 1000000`.

## Relation to the Library

- `exists_norm_inducedOrbitWavePacket_le_xi` (`OrbitWavePacket`) is the bound `‖f_ψ‖ ≤ c Ξ`
  without the factor `(1 + ‖n_G‖)^{-r}`, for bounded `w` and finite `ρ`; this module adds that
  factor under the smoothness and coordinate hypotheses above.
- `norm_integral_mul_le_rpow` (`TorusFourierAveraging`) is the abstract averaging estimate; this
  module supplies its hypotheses for the wave packet.
- `norm_twist_coefficientMap_le_xi` (`InducedCoefficientTwistXi`) bounds
  `twistedSectionCoefficient … χ F₀` uniformly in unitary `χ`; it is used, not reproved.

## Open obligations

- The second part of the proof of Prop. VI.3.1 (the estimates near the walls via I.5 and
  Prop. I.4.3 and the constant term, `n(ϕ)`, `n_w(ϕ)`, `n_+(ϕ)` on printed p. 303) and the
  conclusion `f_ψ ∈ C(G)` are not addressed.
- `n_G` (`H_G` in lattice coordinates) with `hnK`, `hnU`, `hnM`, the Plancherel density `µ`,
  the Laurent coordinates `hLaurent`, `hcoeff` (Corollary III.1.2 for `π`) and the Iwasawa and
  Levi data `hL`, `hP₀K`, `hMK`, `hδ₀` are hypotheses.
