# Split component, central quotient and character measures of a lower Levi subgroup

Module `Langlands.HarmonicAnalysis.HarishChandraSchwartz.StandardLeviLowerSplitCenter`, namespace
`Langlands.HarishChandraSchwartz.LowerSplitCenter`. It imports
`StandardLeviLowerChamber` (the chamber `ν'` of the lower Levi), Task 7454's
`RationalWeakExpansionLowerOrbit` (through it), `StandardLeviCharacterMeasure`,
`GeometricLemmaExponentTransfer` and `RationalOrbitCentralFiberAdapter`.

## Purpose and provenance

Waldspurger proves Proposition VI.3.1 by induction. The source is J.-L. Waldspurger, *La formule
de Plancherel pour les groupes p-adiques, d'après Harish-Chandra*, J. Inst. Math. Jussieu 2
(2003), proof on printed pp. 302–305. In the weak-part step on p. 304 he applies the induction
hypothesis to packets on a proper standard Levi subgroup `M' = M_{I'}` for the parabolic
`M' ∩ s·P`, with `s` represented by `n ∈ N_G(S)(F)`.

Task 7454 (`RationalWeakExpansionLowerOrbit`) writes these lower packets on the literal Levi
`(s·M)(F) = Z_{M'}(sζ)(F)` of the lower cocharacter `χ_s = lowerCocharacter i ν (rootSet I') ζ n`.
It conjugates all the data of `M = M_I` by `n`:

- the central subgroup `sC = lowerCentral … C`, the image of `C ≤ M_I(F)` under the conjugation
  `eₛ : M_I(F) ≃ (s·M)(F)`;
- the quotient Haar measure `sμ = lowerMeasure … C μ` on `(s·M)(F)/sC`;
- the representation `sπ = lowerRepresentation … π`;
- the character measure `lowerCharacterMeasure … ρ`, the image of a measure `ρ` on
  `Im X(M_I)` under the conjugation `lowerCharacterConjugation : Im X(M_I) ≃ Im X(s·M)`.

The module `StandardLeviLowerChamber` re-chooses the chamber of `M'`: a generic `ν'` and labels
`J''` for which `sζ` is standard, so that `M_{J''}(ν')(F)` is `Z_{M'}(sζ)(F)`. The
source-normalized target `StandardLeviPlancherelWavePacketSourceNormalizedStatement` at `M'`, `ν'`,
`J''` asks for different data. It asks for a split component `s'` of the literal standard Levi
scheme `M_{J''}`, square integrability modulo `A_{M_{J''}}(F) = rationalLeviSplitCenter J'' s'`,
a Haar measure on the quotient by that subgroup, and the character measure
`standardLeviUnitaryUnramifiedCharacterHaar J'' s' …` of Waldspurger I.1 for `s'`.

This module shows that the two sets of data correspond exactly, without any scalar factor. The
choice is `s' = s ≫ (M_I ≅ M_{J''})`, where `s` is the split component of `M_I` used at `G`.

Provenance is **derived**. Waldspurger states none of these facts: on p. 304 he simply replaces
`G` by `M'` in the definitions. They are needed only because the Library's lower packets and the
Library's target normalize the central data differently. No statement is quoted from the source.
Every result is a consequence of published Library theorems.

## Section `OrbitTransport`: orbits along a multiplicative homeomorphism

The setting is general. `G` and `H` are non-archimedean topological groups, and
`e : H ≃ₜ* G` is a multiplicative homeomorphism. `νG` and `νH` are families of norm characters
of `G` and `H`, possibly indexed by different types, and
`c : Im X(νG) ≃ₜ* Im X(νH)` is a multiplicative homeomorphism of their unitary unramified
character groups with `(c χ)(h) = χ(e h)` (hypothesis `hc`). `A ≤ G` and `B ≤ H` are normal
central subgroups with `e(B) = A` (hypothesis `hAB`). `μG` and `μH` are Haar measures on `G/A` and
`H/B` with `μH` mapped to `μG` by the induced quotient homeomorphism (hypothesis `hμ`). `pb` is
the published pullback of discrete-series classes `DiscreteSeriesClass.pullback e … hμ`.

- `pullback_smul_of_apply`: `pb (χ • ω) = c χ • pb ω`. It is the published
  `SmoothDualClass.pullback_twist`, after identifying `χ ∘ e` with `c χ` through `hc`.
- `map_discreteSeriesStabilizer`: `c` maps the stabilizer of `ω` in `Im X(νG)` onto the
  stabilizer of `pb ω` in `Im X(νH)`. One inclusion is `pullback_smul_of_apply`; the other also
  uses injectivity of `pb` (`DiscreteSeriesClass.pullback_injective`).

From here on, `ω'` is a class modulo `B` and `hω : pb ω = ω'`. The target class is an argument so
that it can be given in any form that is equal to the pullback. In the application it is the
class of `π'`, which equals the pullback by `rfl`.

- `map_discreteSeriesStabilizer_of_eq`: the same statement for `ω'`.
- `card_discreteSeriesStabilizer`: the two stabilizers have the same cardinality.
- `finite_discreteSeriesStabilizer`: if the stabilizer of `ω` is finite, so is that of `ω'`.
- `orbitTransport` is the homeomorphism from the orbit of `ω` under `Im X(νG)` to the orbit of
  `ω'` under `Im X(νH)`. It is built from the published orbit homeomorphisms
  `discreteSeriesOrbitHomeomorph` (orbit = character group modulo stabilizer) and the quotient
  homeomorphism induced by `c` on the character groups.
- `orbitTransport_orbitMap`: it sends `χ • ω` to `c χ • ω'`.
- `orbitTransport_val`: as a class, the image of `x` is `pb x`.
- `map_discreteSeriesOrbitMeasure_orbitTransport`: assume both stabilizers are finite. Then for
  every measure `λ` on `Im X(νG)`, the image of the orbit measure
  `discreteSeriesOrbitMeasure νG A … ω λ` under `orbitTransport` is
  `discreteSeriesOrbitMeasure νH B … ω' (c_* λ)`. The proof unfolds the orbit measure
  (`(card Stab)⁻¹ •` image of `λ` under the orbit map), uses `orbitTransport_orbitMap` and
  `card_discreteSeriesStabilizer`.

## Section `SchemeIso`: the I.1 character measure along an isomorphism

Here `L` and `L'` are affine group schemes, locally of finite type, over a non-archimedean
local field `F`, and `Φ : L ≅ L'` is an isomorphism of group schemes.

- `rationalPoints_map_inv_hom`, `rationalPoints_map_hom_inv`: on rational points, `Φ.hom` and
  `Φ.inv` are mutually inverse.
- `rationalUnitaryCharacterIso Φ : Im X(L) ≃ₜ* Im X(L')` is `z ↦ z ∘ Φ⁻¹` on rational points,
  built from the published restriction maps `rationalUnitaryUnramifiedCharacterRestrict Φ.inv`
  and `… Φ.hom`. `rationalUnitaryCharacterIso_apply` records the formula.
- For a homomorphism `s : T → L` from a commutative affine group scheme,
  `restrict_comp_rationalUnitaryCharacterIso` says that restriction along `s ≫ Φ.hom` after
  `z ↦ z ∘ Φ⁻¹` is restriction along `s`. Hence `card_ker_restrict_comp_iso`: the two
  restriction kernels have the same cardinality.
- `map_rationalUnitaryUnramifiedCharacterHaar_iso`: if `s` is central with the finite-index
  premise, and so is `s ≫ Φ.hom`, then the image of the I.1 measure
  `rationalUnitaryUnramifiedCharacterHaar s …` under `rationalUnitaryCharacterIso Φ` is
  `rationalUnitaryUnramifiedCharacterHaar (s ≫ Φ.hom) …`. By the published
  `rationalUnitaryUnramifiedCharacterHaar_eq_smul_probability`, both are the cardinality of the
  restriction kernel times the probability Haar measure. The kernels have the same cardinality,
  and a continuous surjective homomorphism of compact groups preserves the probability Haar
  measure (`MonoidHom.measurePreserving`).

## Section `Lower`: the lower Levi `M' = M_{I'}` and the chamber of `sζ`

### Setting and notation

The hypotheses are those of Task 7454's lower data: `G` connected reductive (`hG`), `i` a
maximal split torus (`hi`), `ν` generic (`hν`), `I` and `I'` two finite sets of simple-root
labels, `ζ` a standard cocharacter for `I` (`hζ`), and `n` a normalizer point with
`n M_I n⁻¹ ≤ M_{I'}` (`hn`). The two label sets are independent; they need not be nested. The
only relation between them is the containment `hn` of the conjugated Levi in `M_{I'}`, which is
how Waldspurger indexes the weak-expansion summands by `s·M ⊆ M'` (V.1, p. 288) and the
induction on p. 304. For example, in `GL₃` with the diagonal torus and the upper-triangular
chamber, `I = {α₁₂}`, `I' = {α₂₃}` and the permutation matrix of the cycle `1 → 2 → 3 → 1`
satisfy `hn` with equality. In the Lean source:

- `M'` is `Standard.leviScheme i ν (rootSet I')` and `iL` its maximal split torus;
- `c` is `lowerChamber hi I' ζ n`, with chamber `ν'` and labels `J''`;
- `𝐋` is the Levi scheme `M_I` of `G` and `𝐋'` the Levi scheme `M_{J''}(ν')` of `M'`;
- `𝐌` and `𝐌'` are `M_I(F)` and `M_{J''}(F)` as subtypes of `G(F)` and `M'(F)`, written as in the
  target;
- `e₀ = lowerChamberLeviHomeomorph : Z_{M'}(sζ)(F) ≃ₜ* M_{J''}(F)` (from
  `StandardLeviLowerChamber`), and `eₛ = lowerLeviConjugation : M_I(F) ≃ₜ* (s·M)(F)` (Task 7454);
- `Φ₁ = lowerParameterIso : Z_{M'}(sζ) ≅ M_I` (Task 7454) and
  `Φ₂ = standardLeviParameterIso : Z_{M'}(sζ) ≅ M_{J''}` at `M'`, `iL`, `ν'`, `J''`.

The local instances are those of Task 7454's lower-orbit module, so that the topology on
`M'(F)` is the same as there.

### The scheme isomorphism `M_I ≅ M_{J''}`

- `lowerChamberLeviEquiv` is `e₀⁻¹ : M_{J''}(F) ≃ₜ* (s·M)(F)`, with codomain written as the
  literal Levi `levi χ_s` on which Task 7454's data live.
- `rationalPoints_map_comp`: rational points of a composite.
- `leviRationalPointHomeomorph_lowerParameterLeviIso`: on points, `Φ₂` is
  `e₀ ∘ parameterHomeomorph`. It is the published
  `leviRationalPointHomeomorph_map_standardLeviParameterIso`.
- `lowerLeviIso : M_I ≅ M_{J''}` is `Φ₁⁻¹ ≪≫ Φ₂`.
- `leviRationalPointHomeomorph_lowerLeviIso`: on points it is `y ↦ e₀(eₛ(y))`, conjugation by
  `n` followed by `Z_{M'}(sζ)(F) = M_{J''}(F)`. It combines the previous item with Task 7454's
  `leviRationalPointHomeomorph_lowerParameterIso`.
  `lowerChamberLeviEquiv_lowerLeviIso` is the same identity after applying `e₀⁻¹`.

### The split component `s'` and `A_{M_{J''}}(F)`

Let `s : A → M_I` be a homomorphism from a commutative affine group scheme.

- `lowerSplit` is `s' = s ≫ lowerLeviIso.hom : A → M_{J''}`.
- `isSplitComponent_lowerSplit`: if `s` is a split component of `M_I`, then `s'` is one of
  `M_{J''}` (published `IsSplitComponent.comp_iso`).
- `lowerLevi_isConnectedReductive`: `M_{J''}` is connected reductive (published
  `standardLevi_isConnectedReductive` in `M'`).
- `finiteIndex_lowerSplit`: the finite-index premise of the I.1 measure holds for `s'`
  (published `finiteIndex_splitValuationImage_of_isSplitComponent`).
- `map_lowerSplitCenter`: with `C = rationalLeviSplitCenter I s` and
  `C' = rationalLeviSplitCenter J'' s'`, the image of `C'` under `e₀⁻¹` is Task 7454's
  `lowerCentral … C`. This uses the point formula for `lowerLeviIso`.
- `lowerSplitCenter_normal`, `lowerSplit_range_normal`: `C'` and the image of `A(F)` in
  `M_{J''}(F)` are normal, being central.

### The central quotient and square integrability

Assume `C` and `C'` are normal, the quotients carry Borel measurable structures, and `μ` is a
Haar measure on `M_I(F)/C`.

- `lowerChamberQuotientEquiv : M_{J''}(F)/C' ≃ₜ* (s·M)(F)/sC` is induced by `e₀⁻¹`.
- `lowerChamberQuotientMeasure` is the image of `sμ = lowerMeasure … C μ` under the inverse of
  this equivalence. It is a Haar measure (`lowerChamberQuotientMeasure_isHaarMeasure`), and
  `lowerChamberQuotientMeasure_map` says that it is mapped back to `sμ`.
- `lowerChamberRepresentation_isSquareIntegrable`: assume `s` is a split component and `π` is
  square integrable modulo `C` for `μ`. Then `π' = lowerChamberRepresentation … π` is square
  integrable modulo `C'` for `lowerChamberQuotientMeasure`. The proof combines Task 7454's
  `lowerRepresentation_isSquareIntegrable` with the published
  `isSquareIntegrableModCentralSubgroup_comp_iff` along `e₀⁻¹`.

### The I.1 character measures

`eX` and `eX'` denote the published `standardLeviUnitaryCharacterHomeomorph` for `I` and for
`J''` (from the intrinsic character group of the Levi scheme to the character group of the
literal Levi subtype).

- `lowerChamberCharacterTransport : Im X(s·M) ≃ₜ* Im X(M_{J''})` is
  `lowerCharacterConjugation⁻¹`, then `eX⁻¹`, then `rationalUnitaryCharacterIso lowerLeviIso`,
  then `eX'`.
- `lowerChamberCharacterTransport_apply`: the transported character is `z ∘ e₀⁻¹`.
- `map_lowerCharacterMeasure`: assume `s` is a split component with the finite-index premise.
  The image under `lowerChamberCharacterTransport` of
  `lowerCharacterMeasure (standardLeviUnitaryUnramifiedCharacterHaar I s …)` is
  `standardLeviUnitaryUnramifiedCharacterHaar J'' s' …`. The proof unfolds both measures as
  images of the I.1 measures of `s` and `s'`, composes the maps, and applies
  `map_rationalUnitaryUnramifiedCharacterHaar_iso` to `lowerLeviIso`.

### The orbits and orbit measures

`sω` is the class of `sπ` modulo `sC` for `sμ` (Task 7454's lower orbit is the orbit of `sω`),
and `ω'` is the class of `π'` modulo `C'` for `lowerChamberQuotientMeasure`.

- `pullback_lowerClass`: `ω'` is the pullback of `sω` along `e₀⁻¹`, by `rfl`.
- `lowerChamberOrbitTransport` is `orbitTransport` for `e₀⁻¹` and
  `lowerChamberCharacterTransport`: a homeomorphism from Task 7454's lower orbit of `sω` under
  `Im X(s·M)` to the orbit of `ω'` under `Im X(M_{J''})`.
- `lowerChamberOrbitTransport_orbitMap`: it sends `z • sω` to
  `lowerChamberCharacterTransport z • ω'`.
- `finite_lowerChamberStabilizer`: the stabilizer of `ω'` is finite when that of `sω` is.
- `map_lowerOrbitMeasure`: assume both stabilizers are finite. The image under
  `lowerChamberOrbitTransport` of Task 7454's orbit measure of `sω` for
  `lowerCharacterMeasure (standardLeviUnitaryUnramifiedCharacterHaar I s …)` is the orbit measure
  of `ω'` for `standardLeviUnitaryUnramifiedCharacterHaar J'' s' …`. This is the orbit measure
  `dO'` that the target uses at `M'`. The proof is
  `map_discreteSeriesOrbitMeasure_orbitTransport` followed by `map_lowerCharacterMeasure`.

`map_lowerCharacterMeasure` and `map_lowerOrbitMeasure` raise `maxHeartbeats` to 800000 and
1000000. Both proofs are short chains of equalities, but every step elaborates terms that contain
the full lower-Levi data of Task 7454. They need about 530000 and 670000 heartbeats.

## What this module does not provide

- It does not compare the target's section spaces `rationalInducedSmoothOrbitSections` at `M'`
  with Task 7454's dynamic lower sections, and it does not compare the wave packets. That is a
  separate module.
- It does not compare Task 7454's `lowerPlancherelWeight` with the target's weights at `M'`.
- The finiteness of the stabilizer of `sω` is a hypothesis here. Task 7454's
  `finite_lowerStabilizer` derives it from the finiteness of the stabilizer of the class of `π`.
- It proves nothing analytic and does not prove the host target.
