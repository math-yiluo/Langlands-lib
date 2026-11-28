# The weighted identity at a regular orbit point from four inputs

Lean module: `Langlands.HarmonicAnalysis.HarishChandraSchwartz.RationalWeakExpansionRegularPointInputs`,
namespace `Langlands.HarishChandraSchwartz.WeakExpansion`.

## Purpose and contents

`WeightedWeakExpansionRegularIdentityStatement` (module `RationalWeakExpansionRegularIdentity`)
is the weighted identity

`µ^G(ω) (f_ω)^w_{P'}(m') = Σ_s µ^{M'}(sω) (E^{M'}_{M'∩s·P} Ψ_{s, sω})(m')`

of Waldspurger's proof of VI.3.1 (printed p.304) at the orbit points `ω = π ⊗ χ` for which
`π ⊗ χ` is regular for the literal normalizer of `M_I(F)` in `G(F)` (`χ ∈ regularUnitaryTwists`).
In the source it follows from Proposition V.1.1 (printed p.289) by multiplication with `µ^G(ω)`
and the definition of `c̃ = µ^G µ^{M'}(s·)⁻¹ c` in Corollary V.2.3 (printed p.294). This module
states V.1.1 at a regular point with the Library's objects, three auxiliary facts, and proves that
the four statements give the weighted identity at the regular points.

The section variables and local instances are those of `RationalWeakExpansionTargets` and
`RationalWeakExpansionRegularIdentity`. Throughout, `s` is a Weyl index, `n = R.normalizer s` its
lift, `χ_s = lowerCocharacter … n` the lower cocharacter with parabolic `M' ∩ s·P`, and
`e_s = lowerLeviConjugation` the conjugation `M_I(F) ≃ s·M(F)`. The compact pictures are the
published `ProductInducedCompactPicture`: `I^{K×K}_{K∩P×K∩P}(E ⊗ Ě)` of `π` on `G`, and the
lower compact picture of `sπ = π ∘ e_s⁻¹` on `M'` for the compact open subgroup `lowerK PM` of
the lower density package.

## Definitions

**`lowerCompactCFamily`.** For `z` in the joint convergence domain `cDomain … π.obj`, the
published `cCompactFamily` of `π` at `z` (the c-map `c_{P'|P}(s, π ⊗ z)` of
`RationalWeakExpansionCFamily`, read on the compact pictures) with the lower compact subgroup
`lowerK PM` and its Iwasawa decomposition (`lowerK_isCompact`, `lowerPackage_iwasawa`). It is
the unweighted counterpart of `weightedCompactFamily`.

**`CExtensionAt … PM χ`** (structure), for a unitary unramified character `χ` of `M_I(F)`:
the fields are

- `interior_nonempty`: the interior of `cDomain … π.obj` is nonempty;
- `denominator : unramifiedRegularFunctions νM` and a numerator
  `numerator z` (linear maps between the two compact pictures) for every unramified `z`,
  polynomial in `z` (`UnramifiedOperatorFamily.IsPolynomialOperatorOn Set.univ`);
- `clears`: `numerator w = denominator(w) • lowerCompactCFamily w` for every `w` in the interior
  of `cDomain`;
- `regular`: `denominator(χ) ≠ 0`.

It has the form of the published `WeightedCExtension`, for the unweighted family, with
regularity required only at `χ`. `CExtensionAt.value C = denominator(χ)⁻¹ • numerator(χ)` is the
value at `χ`. **`CExtensionAt.value_eq`** (proved): two extensions at `χ` have the same value. The
proof is the published `leviRationalContinuation_value_eq` (identity theorem on `X(M_I)`), as for
`WeightedCExtension.unitaryValue_eq`.

**Provenance.** Waldspurger, printed p.289: "L'opérateur `c_{P'|P}(s, ω)` est rationnel en `ω`. Il
est régulier aux points `G`-réguliers de `O`, d'après la proposition IV.2.2." `CExtensionAt`
expresses rationality and regularity at one point in the form used by the Library for `c̃`.

**`compactCoefficient … χ`.** The linear map from the compact picture of `π` to
`LocallyConstant G(F) ℂ`: the published `rationalInducedCoefficientMap` of `π ⊗ χ` (with the
admissibility of the twist, `SmoothRep.isAdmissible_twist_iff`) composed with the inverse of the
published `productInducedCompactEquiv` at `χ`. It is `E^G_P` of the element of `L(π ⊗ χ, P)`
with the given compact picture.

**`lowerCompactCoefficient … PM χ`.** The linear map from the lower compact picture of `sπ` to
`LocallyConstant M'(F) ℂ`: the published `CompactInduction.coefficientMap` for the dynamic
parabolic of `χ_s` (decomposition `decomposition χ_s`, compact subgroup `lowerK PM`, the
unimodularity `rationalReductiveUnimodularity` of `M'(F)` and the modular character
`DynamicInducedOrbit.parabolic_modularCharacter_eq`), for the twist of `sπ` by
`sχ = lowerUnramifiedCharacterConjugation χ`, composed with the inverse of
`productInducedCompactEquiv` at `sχ`. These are the arguments with which
`DynamicInducedOrbit.inducedOrbitCoefficientMap` is formed; the Borel structure and the local
compactness of the parabolic are the instances of `DynamicInducedOrbitWavePacket`
(`dynamicInducedOrbitMeasurableSpace`, `dynamicInducedOrbitBorelSpace`,
`dynamicInducedOrbitParabolicLocallyCompact`). It is `E^{M'}_{M'∩s·P}` of the element of
`L^{M'}(s(π ⊗ χ), M' ∩ s·P)` with the given compact picture.

## The four statements

Write `ω = discreteSeriesOrbitMap … χ` for the orbit point `π ⊗ χ`, `Wπ` for the weight `µ^G`
(`standardLeviPlancherelWeight` with the fields of `PG`), `lowerPlancherelWeight … (PM s)` for
`µ^{M'}` and `lowerOrbitMap … ω` for `sω`.

**`UnweightedRegularPointIdentityStatement`** (explicit arguments
`hG hi hν I I' hζ hζ' hKc hPK sc hs π mu hsq hRefl hCST PG hA R PM`; instance arguments include
`[MeasurableSpace (M(F)/C_M)] [BorelSpace (M(F)/C_M)]`, bound explicitly, so the measurable
structure of the inducing Levi's split-center quotient is its Borel structure, `mu` is a Haar
measure for it and `hsq` is square integrability modulo `C_M` in the sense of Waldspurger III.1,
printed p.263). If `I'` is proper,
`IsSpecialVertexCompact ν hi K`, `LiftsInCompact R` and `SourceCompactNormalization …` hold,
then for every `χ ∈ regularUnitaryTwists i ν I π.obj`, every family `C s : CExtensionAt … (PM s) χ`,
every section `q ∈ C^∞(O, P)` and every `m' ∈ M'(F)`:

`rationalOrbitWeakConstantTerm … q ω (leviRationalPointHomeomorph i ν I' m')
  = Σ_s lowerCompactCoefficient … (PM s) χ ((C s).value (sectionCompactPicture … q χ)) m'`.

This is Proposition V.1.1, `(E^G_P ψ)^{w,Ind}_{P'} = Σ_s E^{P'}_{M'∩s·P}(c_{P'|P}(s, ω)ψ)` at a
`G`-regular `ω`, evaluated at `(1, 1)` and restricted to `M'(F)` (the form of printed p.304), with
`ψ = q_ω` given by its compact picture at `χ` and `c_{P'|P}(s, ω)` the value of a rational
extension regular at `χ`. The common source normalization makes `E^{M'}` the coefficient formed
with `K ∩ M'(F)`, as in the source.

**`CExtensionAtRegularStatement`** (explicit arguments
`hG hi hν I I' hζ hζ' hKc hPK sc hs π mu hRefl hCST R PM`; as above, the instance argument
`[BorelSpace (M(F)/C_M)]` is bound explicitly). If `π` is square integrable modulo `C_M` for the
Haar measure `mu` on the topological quotient `M(F)/C_M` with its Borel structure (the
square-integrable representations of III.1, printed p.263), then for every `χ ∈ regularUnitaryTwists i ν I π.obj` and every Weyl index `s` there is an
extension `CExtensionAt … (PM s) χ`. Source: printed p.289 (quoted above); Proposition IV.2.2(ii)
(printed p.284): for `π` irreducible, square integrable and `G`-regular, the rational operator
`J_{P'|P}` is regular at `π`; IV.1 (12), (14) for the composite. The nonemptiness of the
convergence domain is Proposition IV.2.1.

**`WeightedCValueRelationStatement`** (explicit arguments
`hG hi hν I I' hζ hζ' hKc hPK sc hs π mu hsq hRefl hCST PG R PM`). For every
`hN : SourceCompactNormalization …`, every Weyl index `s`, every `E : WeightedCExtension … (hN s)`,
every unitary unramified `χ` and every `C : CExtensionAt … (PM s) χ`:

`lowerPlancherelWeight … (PM s) (sω) • E.unitaryValue χ = Wπ ω • C.value`

as linear maps between the compact pictures. Source: Corollary V.2.3 (printed p.294) defines
`c̃_{P'|P}(s, ω) = µ^G(ω) µ^{M'}(sω)⁻¹ c_{P'|P}(s, ω)` as a rational function; hence
`µ^{M'}(s·) c̃ = µ^G c` as rational functions, and both sides are regular at `χ` (the densities
are regular at unitary characters, `E` is regular on the unitary orbit and `C` at `χ`). The
statement holds at every unitary `χ`, regular or not, including the zeros of the densities.

**`LowerCoefficientCompactPictureStatement`** (explicit arguments
`hG hi hν I I' hζ sc hs π mu hsq hRefl hCST R PM`). For every Weyl index `s`, every lower section
`Ψ : LowerSections … s`, every unitary unramified `χ` and every `m' ∈ M'(F)`:

`DynamicInducedOrbit.inducedOrbitCoefficientMap … Ψ (sω) m'
  = lowerCompactCoefficient … (PM s) χ (dynamicSectionCompactPicture … Ψ
      (leviUnitaryCoordinates … (lowerCharacterConjugation … χ))) m'`.

This is the compatibility of the Library's orbit coefficients with the compact pictures: the
orbit coefficient at `sω` is the coefficient of the value of `Ψ` at a representative of `sω`
(compare `unitaryOrbitCoefficientMap_representative`), and that value is recovered from its
compact picture at `sχ`.

## The proved reduction

**Theorem `weightedWeakExpansionRegularIdentity_of_inputs`.** Hypotheses: the four statements
above for the data of the conclusion. Conclusion:
`WeightedWeakExpansionRegularIdentityStatement hG hi hν I I' hζ hζ' hKc hPK sc hs π mu hsq hRefl
hCST PG hA R PM`.

Proof as implemented. Introduce the premises, `q`, `E`, `Ψ`, the section formulas `hsec`, `m'`
and `χ` with its regularity.

1. `CExtensionAtRegularStatement` (with the square integrability `hsq`) gives, by choice, an
   extension `C s` regular at `χ` for every `s`.
2. `UnweightedRegularPointIdentityStatement` rewrites the weak constant term as the sum over `s`
   of `lowerCompactCoefficient … χ ((C s).value φ) m'`, with `φ` the compact picture of `q` at
   `χ`; `Finset.mul_sum` distributes `µ^G(ω)`.
3. For each `s`, `LowerCoefficientCompactPictureStatement` rewrites the lower orbit coefficient of
   `Ψ s` as `lowerCompactCoefficient` of its compact picture, and `hsec s χ`
   (`IsWeightedCSection`) replaces that compact picture by `(E s).unitaryValue χ φ`.
4. `WeightedCValueRelationStatement`, applied under `lowerCompactCoefficient … χ (· φ) m'` with
   `congrArg`, and the linearity of the coefficient map (`LinearMap.smul_apply`, `map_smul`,
   `LocallyConstant.smul_apply`) identify the two summands.

The equation is proved for terms elaborated in this module and then closes the membership goal
of `WeightedWeakExpansionRegularIdentityStatement` (`Set.mem_ofPred`) at reducible transparency:
the two expressions differ only in automatically generated auxiliary proof constants.

## Source

J.-L. Waldspurger, *La formule de Plancherel pour les groupes p-adiques, d'après Harish-Chandra*,
J. Inst. Math. Jussieu 2 (2003), 235–333, registered as `waldspurger-2003-plancherel`, PDF SHA-256
`4b6a6162cd0b3863703fb2f65d1698f926caf813114917f2084c16e38f2e30f7` (PDF page = printed page −
234): IV.1 (12), (14) and Propositions IV.2.1, IV.2.2 (printed p.284); the definition of
`c_{P'|P}(s, ω)` and Proposition V.1.1 with its proof, printed pp.288–292; Corollary V.2.3,
printed p.294; the weighted identity in the proof of VI.3.1, printed p.304.
