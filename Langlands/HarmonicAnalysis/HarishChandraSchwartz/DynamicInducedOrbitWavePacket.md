# Orbit sections, coefficients and wave packets for actual dynamic parabolics

Author: Worker 131, task `b2eba110-082e-4b07-9076-f64b90cd0dc3` (Task 7454, revision 1).

Lean module: `Langlands.HarmonicAnalysis.HarishChandraSchwartz.DynamicInducedOrbitWavePacket`,
namespace `Langlands.HarishChandraSchwartz.DynamicInducedOrbit`.

## Purpose

Task 7454 states Waldspurger's expansion (Proposition V.1.1, Corollary V.2.3) of weighted weak
constant terms into wave packets of a *lower* Levi group `M'`. On `M'` these packets are induced
from the parabolic `M' ∩ s·P`, which is in general only *semistandard* in `M'`. The published
constructions in `RationalInducedOrbitWavePacket` cover only actual *standard* parabolics `P_I`.
The objective (item 2) allows either extending the section, coefficient and wave-packet
constructions to semistandard parabolics or a transport to standard data. This module does the
extension. It works for any parabolic of the form `P(χ)`, the dynamic parabolic of a cocharacter.
This covers every semistandard parabolic, `M' ∩ s·P` included: such a parabolic is `P(χ')` for a
suitable cocharacter `χ'` of the maximal split torus.

The module instantiates the abstract constructions of `ProductInducedOrbitSections`,
`ProductInducedOrbitCoefficients` and `OrbitWavePacket`. The instantiation follows the pattern of
`RationalInducedOrbitWavePacket`. The actual dynamic subgroups and their topology come from
`DynamicOppositeStandardIntertwining` and `DynamicOppositeCanonicalScalar`.

## Data

All declarations are generic in:

- a nonarchimedean local field `F : Type u` (any characteristic);
- an affine group scheme `H` over `Spec F` of locally finite type with
  `hH : IsConnectedReductive H`;
- a cocharacter `χ : 𝔾_m ⟶ H` (`(Gm (Spec (CommRingCat.of F))).toGrp ⟶ H`).

Neither split nor quasisplit `H` is assumed. The actual subgroups of `H(F)` used are the
published abbreviations of `Langlands.Plancherel.DynamicOppositeStandardIntertwining`:
`parabolic χ = P(χ)(F)`, `levi χ = Z_H(χ)(F)`, `radical χ = U(χ)(F)`, and their decomposition
`decomposition χ : P(χ)(F) = Z_H(χ)(F) ⋉ U(χ)(F)`. The norm characters of the Levi are
`leviNormCharacters χ`, the characters `|ψ|_F` of `Z_H(χ)(F)` for `ψ` a rational character of the
centralizer scheme `parameterScheme χ`, transported along the point homeomorphism
`parameterHomeomorph χ`.

The sections and coefficients also take:

- a compact open subgroup `K` of `H(F)` (`hK`) with `H(F) = P(χ)(F) K` (`hPK`);
- an irreducible admissible complex representation `π` of `Z_H(χ)(F)`, with carrier universe
  `uV` independent of the field universe `u`;
- for coefficients and packets, a central subgroup `C` of `Z_H(χ)(F)` (`hC`), a Haar measure `mu`
  on the quotient by `C`, and square integrability of `π` modulo `C` (`hsq`). This is the
  Library's `IsSquareIntegrableModCentralSubgroup`.

## Definitions and results

- `leviUnitaryCoordinates hH χ` (new definition). It gives circle coordinates on
  `Im X(Z_H(χ))`, the group of unitary unramified characters for `leviNormCharacters χ`. It is the
  composite of the transport `unitaryUnramifiedCharactersHomeomorph (parameterHomeomorph χ)
  (normCharacters χ)` (from `RationalInducedOrbitWavePacket`) with the Library's canonical
  coordinates `rationalCanonicalUnitaryUnramifiedCharacterCoordinates` of the reductive
  centralizer scheme. The centralizer is reductive by `parameterScheme_isConnectedReductive`.
- `leviUnitaryCoordinates_hasLaurent` (proved). These coordinates satisfy
  `HasLaurentUnitaryCoordinates`: evaluation of a character at a point is a Laurent monomial in
  the coordinates. The proof transports the published
  `rationalCanonicalUnitaryUnramifiedCharacterCoordinates_hasLaurent` with
  `hasLaurentUnitaryCoordinates_transport`.
- `leviNormCharacters_continuous` (proved). The literal Levi norm characters are continuous. This
  is `normCharacters_continuous` composed with the inverse point homeomorphism.
- `parabolic_modularCharacter_eq` (proved). The modular character of `P(χ)(F)` is the Haar
  modulus of conjugation on its radical:
  `modularCharacter p = HaarModulus.closedRestrictCharacter (radical χ) … p`. The proof is
  `SemidirectModularCharacter.modularCharacter_eq_restrictCharacter_of_unimodular` applied with
  the unimodularity of the Levi (`DynamicOppositeHermitianAdjunctionProof.levi_modularCharacter_eq_one`)
  and of the radical (`radical_unimodular`). This is the modular-character hypothesis `hδ` of the
  abstract coefficient constructions.
- `inducedSmoothOrbitSections hH χ hK hPK π` (new abbreviation): Waldspurger's `C^∞(O, P)` of
  VI.1 for `P = P(χ)(F)`. It is the Library's `productInducedSmoothOrbitSections` with
  `G = H(F)`, `M = Z_H(χ)(F)`, the norm characters `leviNormCharacters χ`, the coordinates
  `leviUnitaryCoordinates`, the actual decomposition and closedness facts, `K`, and `hPK`.
- `inducedOrbitCoefficientMap hH χ hK hPK π C hC mu hsq` (new abbreviation): the coefficients
  `ω ↦ E^H_{P(χ)} ψ_ω` on the orbit. It is the Library's `unitaryOrbitCoefficientMap` on the same
  data. Unimodularity of `H(F)` comes from the published theorem
  `RationalPointFamily.rationalReductiveUnimodularity`, and the modular character from
  `parabolic_modularCharacter_eq`.
- `inducedOrbitWavePacket hH χ hK hPK π C hC mu hsq ρ w q h` (new definition): the wave packet
  `f_ψ(h) = ∫_O w(ω) (E^H_{P(χ)} ψ_ω)(h) dω`. It is the Library's `inducedOrbitWavePacket`
  (`OrbitWavePacket`) for a measure `ρ` on `Im X(Z_H(χ))`, a weight `w` on the orbit
  `discreteSeriesOrbit C hC mu (leviNormCharacters χ) (discreteSeriesClass C hC mu π hsq)`, and a
  section `q`. The orbit measure is `discreteSeriesOrbitMeasure … ρ`, the image of `ρ` under the
  orbit map, normalized as in `OrbitWavePacket`. It requires the stabilizer of the class of `π`
  in `Im X(Z_H(χ))` to be finite, as a typeclass argument, as the abstract construction does.
- `inducedOrbitWavePacket_apply` (proved, by `rfl`): the integral formula above.

## Comparison with the source

J.-L. Waldspurger, *La formule de Plancherel pour les groupes p-adiques, d'après Harish-Chandra*,
J. Inst. Math. Jussieu 2 (2003), 235–333 (literature id `waldspurger-2003-plancherel`). Page
numbers are printed pages.

VI.1, printed p. 295, sets up the sections for any semistandard parabolic: "Soient `P = MU` un
sous-groupe parabolique semi-standard de `G` et `O ∈ E₂(M)` une orbite pour l'action de
`Im X(M)`." Printed p. 296: "Pour tout `χ ∈ Im X(M)`, `L(ω ⊗ χ, P)` s'identifie à `L_K(ω, P)`
par restriction à `K`. La fonction `ψ` s'identifie à une fonction sur `Im X(M)` à valeurs dans
`L_K(ω, P)`. Alors `ψ` est `C^∞` si cette dernière fonction l'est." This is the space
`productInducedSmoothOrbitSections`, here for `P = P(χ)(F)`. The wave packet of VI.3, printed
p. 302, is `f_ψ(g) = ∫_O µ(ω) (E^G_P ψ_ω)(g) dω` for a weight `µ`. Here the weight is the
explicit argument `w`.

The cocharacter description of semistandard parabolics is standard: a semistandard parabolic
`P = MU` of a reductive group with maximal split torus `S` is `P(χ)` for a cocharacter `χ` of `S`
that is positive on the roots of `U` and zero on those of `M`. This module does not prove it.
It only provides the constructions for every `P(χ)`. The caller supplies the cocharacter.

## Status

- Imported proofs: `rationalReductiveUnimodularity`, `levi_modularCharacter_eq_one`,
  `radical_unimodular`, `parabolic_isClosed`, `radical_isClosed`, `projection_continuous`,
  `normCharacters_continuous`, `parameterScheme_isConnectedReductive`,
  `rationalCanonicalUnitaryUnramifiedCharacterCoordinates_hasLaurent`.
- Imported constructions: `productInducedSmoothOrbitSections`, `unitaryOrbitCoefficientMap`,
  `inducedOrbitWavePacket`, `discreteSeriesOrbitMeasure`, `unitaryUnramifiedCharactersHomeomorph`.
- New definitions: `leviUnitaryCoordinates`, `inducedSmoothOrbitSections`,
  `inducedOrbitCoefficientMap`, `inducedOrbitWavePacket`.
- New proved lemmas: `leviUnitaryCoordinates_hasLaurent`, `leviNormCharacters_continuous`,
  `parabolic_modularCharacter_eq`, `inducedOrbitWavePacket_apply`.
- No targets are stated here. The task's targets use these constructions with `H = M'` and the
  cocharacter of `M' ∩ s·P`, in later modules of Task 7454.
